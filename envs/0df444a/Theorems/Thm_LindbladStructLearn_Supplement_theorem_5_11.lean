-- Prove2me | Theorems.Thm_LindbladStructLearn_Supplement_theorem_5_11
-- name    : LindbladStructLearn.Supplement.theorem_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:44:12.401585+00:00
-- url     : https://prove2.me/theorems/af4cffc0-7f2a-4060-8051-d8322b26e94f
-- title:
--   Theorem 5.11 — Algorithm 5 learns a Hamiltonian to $\varepsilon$ in $\infty$-norm, real-time and Gibbs settings (corrected: Jacobian hypothesis at radius $2g$ with $c_{2g}$)
-- statement:
--   Let $\varepsilon>0$ and let $H=i\sum_P\lambda_PP$ be a $k$-local Hamiltonian on $n$ qubits with purely imaginary coefficients, $\|\lambda\|_{B_1}\le g$ and $\|\lambda\|_\infty\le1$. Let $S_H=\{Q:\lambda_Q\ne0\}$ be its support, which the algorithm does not know. Let $c>0$; it plays the role of the paper's constant $c_{2g}$. Let $T=\lceil\log_2(1/\varepsilon)\rceil$, and let $x^{(j)}$ be the iterates of Algorithm 5 run with estimates $\widehat{\mathcal F}_j$ in round $j$.
--
--   1. **Real time.** Let $0<t<1/(20c)$. Suppose that $\|\mathcal F(x^{(j)})-\widehat{\mathcal F}_j(x^{(j)})\|_\infty\le\varepsilon/20$ for every $j<T$. Suppose also that for every $x$ with $\|x\|_{B_1}\le 2g$ and every $P\in\mathcal P_k$,
--   $$\sum_{Q\in S_H}\big|J_{P,Q}(x)-\delta_{P,Q}\big|\le c\,t.$$
--   Then $\|x^{(T)}-\lambda\|_\infty\le\varepsilon$.
--   2. **Gibbs states.** The same holds with $\beta$ in place of $t$ and the Gibbs error vector $\mathcal F$, under the additional requirement that $\operatorname{tr}(e^{-\beta H(x)})\ne0$ for every such $x$ (so that $\mathcal F$ and $J$ are defined there).
--
--   Here $\mathcal F$ and $J$ are the error vector and its Jacobian for the respective access model (Eqs. (5.126)–(5.127)). The theorem reduces Hamiltonian structure learning to two inputs: accurate estimates of $\mathcal F$, and a Jacobian close to the identity on the unknown support. Theorems 5.13 and 5.18 supply both.
--
--   **Formalization Note** Iterates and estimates are complex vectors on $\mathcal P_k$, $J$ is the holomorphic Jacobian, and $\|\cdot\|_\infty$ is the sup norm.
--
--   Differences from the source:
--   - correction: c_g > 0 a constant depending on g; 0 < t, β < 1/(20c_{2g}); hypothesis (5.131) for every x with ∥x∥_B1 ≤ g with bound c_g t (resp. c_g β) → one constant c > 0 (the paper's c_{2g}); 0 < t, β < 1/(20c); hypothesis for every x with ∥x∥_B1 ≤ 2g with bound c t (resp. c β); reason: the proof applies the hypothesis at λ + sΔ with ∥λ + sΔ∥_B1 ≤ 2g and the constant c_{2g} (Lemma 5.12, p.47). As printed the statement is false: n = k = 1, λ_Z = i, g = 1, ε = 1/4, t = 32, F̂ = F; take c_{2g} = 1/(40t) (so t < 1/(20c_{2g})) and c_g = 1 + max over the compact radius-g ball of Σ|J − δ|/t; every hypothesis holds, but |F_P(0)| = |E_P(0) − E_P(λ)|/t ≤ 2/t = 1/16 ≤ ε_j/4 for j < T = 2, so Round sets every entry to 0, all iterates are 0 and ∥0 − λ∥_∞ = 1 > ε. The radius-2g reading is implied by "the bound holds at every radius r with c_r"
--   - reading: Gibbs error vector F_P(x) = −E_P(x)/β + E_P(λ)/β (5.127), with footnote 10: the sign makes the first-order term x_P → F_P(x) = (i/β)(E_P(x) − E_P(λ)); reason: with H(x) = iΣx_P P, E_P(x) = −iβx_P + O(β²), so the printed formula has first-order term i(x_P − λ_P), contradicting footnote 10, and its Jacobian is near iI, so (5.131) fails for every λ ≠ 0 once cβ < 1/20; i/β is the normalization footnote 10 states
--   - encoding: x^(0) = 0 ∈ R^M; inputs x ∈ [−1,1]^m (Claim 5.16) → iterates, estimates and query points are complex vectors on the k-local non-identity Paulis; J is the holomorphic derivative; reason: λ is purely imaginary, so the iterates live in C^m (Section 5); F is holomorphic, so the Fundamental Theorem of Calculus step of Lemma 5.12 is along a complex segment
--   - encoding: (5.131) for the Gibbs state setting → tr(e^(−βH(x))) ≠ 0 and the sum bound, for every x with ∥x∥_B1 ≤ 2g; reason: (5.131) presupposes that J(x) exists, i.e. that ρ_β(x) is defined
--   - generalization: estimates F̂(x) for given inputs x with ∥F(x) − F̂(x)∥_∞ ≤ ε/20 → round-dependent estimates F̂_j, accurate only at the iterates x^(j), j < T; reason: the proof evaluates F̂ only at the iterates; the printed hypothesis is the special case F̂_j = F̂ (as in the published Theorem 5.2)
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 5.11, p.47; Algorithm 5, Eqs. (5.126)–(5.129), p.46; Lemma 5.12 and proof, pp.47–48

import Mathlib
import Definitions.Def_LindbladStructLearn_Supplement_HamiltonianF
import Definitions.Def_LindbladStructLearn_b1Norm

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix

namespace LindbladStructLearn.Supplement

open LindbladTolerant.Testing LindbladStructLearn

/-- Theorem 5.11 (structure learning of Hamiltonians; Lewis–Tang–Wright, *Learning the structure of
open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.47; Algorithm 5,
p.46). Let `ε > 0` and let `H = i Σ_P λ_P P` be a `k`-local Hamiltonian with `‖λ‖_B1 ≤ g` and
`‖λ‖_∞ ≤ 1`, with unknown support `S_H = {Q : λ_Q ≠ 0}`. Let `c > 0` and `0 < t, β < 1/(20c)`. If the
estimates satisfy `‖F(x) − F̂(x)‖_∞ ≤ ε/20` and, for every `x` with `‖x‖_B1 ≤ 2g` and every `P ∈ 𝒫_k`,
`Σ_(Q ∈ S_H) |J_(P,Q)(x) − δ_(P,Q)| ≤ c t` (real time) or `≤ c β` (Gibbs states), then Algorithm 5
finds `λ̂` with `‖λ̂ − λ‖_∞ ≤ ε`. Both settings are stated, as two conjuncts.

**Formalization Note**
1. `c` plays the role of the paper's `c_(2g)`: the hypothesis (5.131) is required at radius `2g` with
   the constant `c_(2g)` of the time bound, which is where Lemma 5.12 and the proof (p.47) use it. The
   printed radius-`g` hypothesis with `c_g` is not enough (see the item's differences).
2. The iterates and estimates are complex vectors on the `k`-local non-identity Paulis; `λ` is purely
   imaginary (`H` Hermitian). `‖·‖` on vectors is the sup norm. `J` is the holomorphic Jacobian
   (`jac`). In the Gibbs setting, `F` is defined where `tr(e^(−βH(x))) ≠ 0`, which (5.131) presupposes.
3. The estimates may depend on the round (`F̂ j` in round `j`) and need to be accurate only at the
   iterates `x^(j)`, `j < T = ⌈log₂(1/ε)⌉`. The Gibbs `F` is normalized by `i/β` (see `gibbsF`). -/
theorem theorem_5_11 (n k : ℕ) (ε : ℝ) (hε : 0 < ε) (g : ℝ) (lam : HIdx n k → ℂ)
    (hlam : ∀ P, (lam P).re = 0) (hB1 : b1Norm (hamVec lam) ≤ g) (hinf : ∀ P, ‖lam P‖ ≤ 1)
    (c : ℝ) (hc : 0 < c) :
    (∀ t : ℝ, 0 < t → t < 1 / (20 * c) →
      ∀ Fhat : ℕ → (HIdx n k → ℂ) → (HIdx n k → ℂ),
      (∀ j < ⌈Real.logb 2 (1 / ε)⌉₊,
        ‖rtF t lam (alg5Iter Fhat j) - Fhat j (alg5Iter Fhat j)‖ ≤ ε / 20) →
      (∀ x : HIdx n k → ℂ, b1Norm (hamVec x) ≤ 2 * g → ∀ P : HIdx n k,
        ∑ Q ∈ Finset.univ.filter (fun Q => lam Q ≠ 0),
          ‖jac (rtF t lam) x P Q - (if P = Q then 1 else 0)‖ ≤ c * t) →
      ‖alg5Iter Fhat ⌈Real.logb 2 (1 / ε)⌉₊ - lam‖ ≤ ε) ∧
    (∀ β : ℝ, 0 < β → β < 1 / (20 * c) →
      ∀ Fhat : ℕ → (HIdx n k → ℂ) → (HIdx n k → ℂ),
      (∀ j < ⌈Real.logb 2 (1 / ε)⌉₊,
        ‖gibbsF β lam (alg5Iter Fhat j) - Fhat j (alg5Iter Fhat j)‖ ≤ ε / 20) →
      (∀ x : HIdx n k → ℂ, b1Norm (hamVec x) ≤ 2 * g →
        (NormedSpace.exp (-(β : ℂ) • hamOp x)).trace ≠ 0 ∧ ∀ P : HIdx n k,
        ∑ Q ∈ Finset.univ.filter (fun Q => lam Q ≠ 0),
          ‖jac (gibbsF β lam) x P Q - (if P = Q then 1 else 0)‖ ≤ c * β) →
      ‖alg5Iter Fhat ⌈Real.logb 2 (1 / ε)⌉₊ - lam‖ ≤ ε) := by sorry

end LindbladStructLearn.Supplement

-- Prove2me | Theorems.Thm_GevreyGibbsSep_Supplement_theorem_A_3
-- name    : GevreyGibbsSep.Supplement.theorem_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:02:34.027085+00:00
-- url     : https://prove2.me/theorems/82ee4b53-1b82-46dc-8e89-3f3aa0ad60d3
-- title:
--   Theorem A.3 — warm-start QSVTh sampler: $O(\sqrt\alpha(\pi N\sqrt d+\beta R)\log(1/\tilde\varepsilon))$ gradient queries, heralded success, $\mathrm{TV}\le\tilde\varepsilon$
-- statement:
--   Let $s\ge1$ and let $p=e^{-\beta E}/Z$ be a Gibbs state on the torus $\mathbb T^d=\mathbb R^d/(2\pi\mathbb Z)^d$ whose potential satisfies (5), i.e. $p\in W^s(\alpha,\xi,\rho)$: the scaled potential $\beta E$ is a $2\pi$-periodic smooth function with Gevrey seminorm $[\beta E]_{s,\rho}\le\xi$ and barrier $\beta\Delta\le\log\alpha$. Let
--   $$
--   R:=\max_x\|\nabla E(x)\|
--   $$
--   (Euclidean norm). Let $|\sqrt{p_N}\rangle$ be the normalized grid Gibbs state on the grid $\tfrac{2\pi}{2N+1}\{-N,\dots,N\}^d$, and let $O_{\nabla E}:|x\rangle|b\rangle\mapsto|x\rangle|b\oplus\nabla E(x)\rangle$ be the gradient oracle.
--
--   **Theorem A.3.** For every overlap constant $c>0$ there are constants $C,C',p_0>0$ and $m\in\mathbb N$, depending only on $s$ and $c$, with the following property. For every $d\ge1$, $\alpha\ge1$, $\xi,\rho,\beta>0$, $0<\tilde\varepsilon<1/2$, $R\ge0$ and every integer grid size
--   $$
--   N\;\ge\;C'\,\frac{d+\xi}{\rho}\Big[ds+\log\frac{\alpha(1+\xi/\rho)}{\tilde\varepsilon}\Big]^s\Lambda^m,\qquad \Lambda=\log\Big(e+d+\alpha+\xi+\rho+\frac1\rho+\frac1{\tilde\varepsilon}\Big),
--   $$
--   there is a warm-started quantum algorithm making
--   $$
--   M\;\le\;C\sqrt\alpha\,\big(\pi N\sqrt d+\beta R\big)\log\frac1{\tilde\varepsilon}
--   $$
--   queries to $O_{\nabla E}$ or its inverse such that, for every potential $E$ with $p\in W^s(\alpha,\xi,\rho)$ and $\max_x\|\nabla E(x)\|=R$, and for every unit warm-start state $|\phi\rangle$ with
--   $$
--   |\langle\phi|\sqrt{p_N}\rangle|\ge c,
--   $$
--   the algorithm, given one copy of $|\phi\rangle$, succeeds (heralded) with probability at least $p_0$, and on success returns a sample $X\sim\eta$ with
--   $$
--   \mathrm{TV}(\eta,p)\le\tilde\varepsilon .
--   $$
--
--   This is the per-step cost of the paper's annealed quantum Gibbs sampler: each annealing step starts from the previous step's state, which has constant overlap with the next grid Gibbs state (Lemma A.8), and Theorem A.3 bounds the gradient queries needed to filter it.
--
--   **Formalization Note** The algorithm is chosen from $(d,s,\alpha,\xi,\rho,\beta,\tilde\varepsilon,N,R,c)$ before the instance; the instance enters only through the oracle and the warm start through an instance-independent loading isometry. The register is $\ell^2(\mathbb R^d\times\mathbb R^d\times W)$ with $\oplus$ read as addition, as in the published model of the mission.
--
--   Differences from the source:
--
--   - reading: |⟨ϕ|√p_N⟩| = Ω(1) → for every c > 0 (constants may depend on c): all unit ϕ on the N-grid with |⟨ϕ, √p_N⟩| ≥ c, √p_N = finiteGibbsState (E ∘ x_k) β; reason: the asymptotic overlap condition made explicit; the mission reading recorded in SUPPLEMENT.md
--   - reading: on heralded success of constant probability, returns a sample X ∼ η with TV(η, p) ≤ ε̃ → a success flag on the measured basis label; success probability ≥ p₀ > 0 with p₀ depending only on s and c; TV of the output law conditional on success ≤ ε̃; reason: "constant" read as independent of d, α, ξ, ρ, β, N, R, ε̃ and the instance, as in the base readings
--   - reading: M ∈ O(√α(πN√d + βR) log(1/ε̃)) and N ∈ Ω̃(((d+ξ)/ρ)[ds + log(α(1+ξ/ρ)/ε̃)]^s) → T ≤ C·√α(πN√d + βR)·log(1/ε̃) for every integer N ≥ C'·((d+ξ)/ρ)(ds + log(α(1+ξ/ρ)/ε̃))^s·Λ^m, Λ = log(e + d + α + ξ + ρ + 1/ρ + 1/ε̃), with C, C', m depending only on s and c; reason: the published theorem_A_1 / theorem_2 reading of O and Ω̃ with sufficiently large constants
--   - reading: there exists a quantum algorithm (for the given E) → the algorithm is chosen from (d, s, α, ξ, ρ, β, ε̃, N, R, c) before E and ϕ and works for every E with βE ∈ W^s(α, ξ, ρ) and max_x ‖∇E(x)‖ = R, and every admissible ϕ; reason: the uniform reading of the base mission (an algorithm accesses E only through O_∇E); it implies the per-instance existence
--   - reading: ε̃ unrestricted in the statement → 0 < ε̃ < 1/2; reason: the range of Theorem A.1 and Corollary A.4, which the proof applies; log(1/ε̃) > 0 needs ε̃ < 1
--   - encoding: R := max_x ‖∇E(x)‖ → R ≥ 0 a parameter with IsGreatest (range of x ↦ sqrt(∑_i (∂_i E(x))²)) R; reason: Euclidean norm written out (the Lean norm on Fin d → ℝ is the sup norm); the max exists for smooth periodic E; R ≥ 0 excludes only values no E attains
--   - encoding: a quantum algorithm with access to a warm-start state |ϕ⟩ and the oracle O_∇E or its inverse → WarmStartQAlg: instance-independent loading isometry, unitaries U_0..U_T, oracle/inverse choices, herald flag, post-processing kernel; exact-real register ℓ²(ℝ^d × ℝ^d × W) with ⊕ read as addition; reason: the base mission's quantum model (reading R1) with a loaded start state and a success flag
--   - encoding: p = e^{−βE}/Z with E satisfying (5) → (fun x => β * E x) ∈ GibbsClass d s α ξ ρ with 1 ≤ s, 1 ≤ α, 0 < ξ, 0 < ρ, 0 < β, d ≥ 1; p = gibbs (β·E); reason: the published class and Gibbs state of the base mission; the ranges of Definition 2
--   - encoding: the grid size N of |√p_N⟩ and (A77)–(A78) → N : ℕ with 1 ≤ N; reason: the standing convention of Appendix A 1, p.20 ("Throughout, the Fourier cutoff N ≥ 1 is an integer"); no instance of the paper is excluded
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Theorem A.3, Eqs. (A76)–(A78), p.31

import Mathlib
import Definitions.Def_GevreyGibbsSep_gibbs
import Definitions.Def_GevreyGibbsSep_tv
import Definitions.Def_GevreyGibbsSep_GibbsClass
import Definitions.Def_GevreyGibbsSep_grad
import Definitions.Def_GevreyGibbsSep_Grid
import Definitions.Def_GevreyGibbsSep_gridPt
import Definitions.Def_GevreyGibbsSep_finiteGibbsState
import Definitions.Def_GevreyGibbsSep_Supplement_WarmStartQAlg
import Definitions.Def_GevreyGibbsSep_Supplement_wsSuccessProb
import Definitions.Def_GevreyGibbsSep_Supplement_wsSuccessLaw

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

namespace Supplement

/-- Theorem A.3, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Eqs. (A76)–(A78), p.31.
Consider a Gibbs state `p = e^{−βE}/Z` with potential `E` satisfying (5), and let
`R := max_x ‖∇E(x)‖`. There is a quantum algorithm with access to a warm-start state `|ϕ⟩` with
`|⟨ϕ|√p_N⟩| = Ω(1)` that, on heralded success of constant probability, returns a sample
`X ∼ η` with `TV(η, p) ≤ ε̃` after `M ∈ O(√α (πN√d + βR) log(1/ε̃))` queries to `O_∇E` or its
inverse, where `N ∈ Ω̃(((d + ξ)/ρ)[ds + log(α(1 + ξ/ρ)/ε̃)]^s)`.

**Formalization Note** (readings of the mission, SUPPLEMENT.md):
* `|⟨ϕ|√p_N⟩| = Ω(1)`: for every overlap constant `c > 0` the statement holds for all unit `ϕ`
  on the `N`-grid with `|⟨ϕ, √p_N⟩| ≥ c`; `|√p_N⟩` is the normalized grid Gibbs state
  `finiteGibbsState (E ∘ x_k) β`.
* "Constant probability": the heralded success probability is at least `p₀ > 0`; `O(·)` is
  `T ≤ C · √α (πN√d + βR) log(1/ε̃)`; `Ω̃(·)` is `N ≥ C' ((d + ξ)/ρ)(ds + log(α(1+ξ/ρ)/ε̃))^s Λ^m`
  with `Λ = log(e + d + α + ξ + ρ + 1/ρ + 1/ε̃)`, as in the published `theorem_A_1`. The constants
  `C, C', p₀, m` depend only on `s` and `c`.
* The algorithm is fixed from `(d, s, α, ξ, ρ, β, ε̃, N, R, c)` before the instance: it works
  for every `E` with `βE ∈ W^s(α, ξ, ρ)` and `max_x ‖∇E(x)‖ = R` (Euclidean norm), and every
  such `ϕ`, loaded by an instance-independent isometry (one copy).
* `TV(η, p) ≤ ε̃` is for the output law conditional on heralded success.
* `0 < ε̃ < 1/2` is the range of Theorem A.1 and Corollary A.4 that the proof applies. -/
theorem theorem_A_3 :
    ∀ s : ℝ, 1 ≤ s → ∀ c : ℝ, 0 < c →
    ∃ C C' p₀ : ℝ, ∃ m : ℕ, 0 < C ∧ 0 < C' ∧ 0 < p₀ ∧
    ∀ d : ℕ, 0 < d → ∀ α ξ ρ β ε' R : ℝ, 1 ≤ α → 0 < ξ → 0 < ρ → 0 < β →
      0 < ε' → ε' < 1 / 2 → 0 ≤ R →
    ∀ N : ℕ, 1 ≤ N →
      C' * ((d + ξ) / ρ) * (d * s + Real.log (α * (1 + ξ / ρ) / ε')) ^ s
          * Real.log (Real.exp 1 + d + α + ξ + ρ + 1 / ρ + 1 / ε') ^ m ≤ N →
    ∃ (W : Type) (T : ℕ) (A : WarmStartQAlg d W N T),
      (T : ℝ) ≤ C * Real.sqrt α * (Real.pi * N * Real.sqrt d + β * R) * Real.log (1 / ε') ∧
      ∀ E : (Fin d → ℝ) → ℝ, (fun x => β * E x) ∈ GibbsClass d s α ξ ρ →
        IsGreatest (Set.range fun x => Real.sqrt (∑ i, grad E x i ^ 2)) R →
        ∀ ϕ : EuclideanSpace ℂ (Grid d N), ‖ϕ‖ = 1 →
          c ≤ ‖⟪ϕ, finiteGibbsState (fun k => E (gridPt d N k)) β⟫_ℂ‖ →
          ENNReal.ofReal p₀ ≤ wsSuccessProb A E ϕ ∧
          tv (wsSuccessLaw A E ϕ) (gibbs (fun x => β * E x)) ≤ ε' := by sorry

end Supplement

end GevreyGibbsSep

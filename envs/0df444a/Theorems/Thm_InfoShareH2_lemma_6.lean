-- Prove2me | Theorems.Thm_InfoShareH2_lemma_6
-- name    : InfoShareH2.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:07.001714+00:00
-- url     : https://prove2.me/theorems/116e37ae-659e-4793-b19b-b4b3e5f37863
-- title:
--   Lemma 6 — conjugate symmetry of the factors and $Q(1)=B(1)=G(1)=1$ (corrected: Stolz-region limit of $Q$ at $1$ replaces continuity on $\mathbb T$)
-- statement:
--   1. A function $\tilde\psi\in H^2$ is **conjugate-symmetric**, $\tilde\psi(\bar z)=\overline{\tilde\psi(z)}$ for $|z|<1$, if and only if all its coefficients $\tilde\psi_k$ are real.
--   2. If a nonzero $\tilde\psi\in H^2$ is conjugate-symmetric, then its factors $Q$, $B$, $G$ in the factorization of Lemma 2 are conjugate-symmetric.
--   3. If $\tilde\psi\in\tilde\Psi$ satisfies Assumption 2 and $\tilde\psi=QBG$ as in Lemma 2, then
--   $$Q(1):=\lim_{r\to1^-}Q(r)=1,$$
--   $Q(z)\to1$ as $z\to1$ inside every Stolz region $R(K)=\{z\in\mathbb D:|1-z|\le K(1-|z|)\}$, and the radial limits of $B$ and $G$ at $1$ equal $1$.
--
--   The normalization $Q(1)=1$ is what ties the outer factor to the constraint $\sum\tilde\psi_n=1$ in the proof of Theorem 2.
--
--   Differences from the source:
--   - correction: "Q(e^{iλ}) is continuous at λ = 0" → Q(z) → 1 as z → 1 inside every Stolz region R(K) of Definition 6; reason: the printed clause is false: Q = exp Θ with Θ = ∑_k [h_k − h_k(1) + conj h_k(z̄) − conj h_k(1)], h_k(z) = (1 − ρ_k)/(1 − ρ_k e^{−iλ_k} z), λ_k = 2^{−k}, ∑√(1 − ρ_k)/λ_k < ∞, with B = G = 1, lies in Ψ̃ and satisfies Assumption 2, is analytic across T∖{1}, and has Q(e^{iλ_k}) near e as λ_k → 0
--   - reading: "if ψ̃ is conjugate-symmetric, its factors B, G, Q defined in Lemma 2 are conjugate-symmetric" → for nonzero ψ̃ ∈ H² and the factorization of Lemma 2 (G with constant 1); reason: Lemma 2 factorizes nonzero functions only; the normalization is that of Lemma 2
--   - reading: "given Assumptions 1–2" → ψ̃ ∈ Ψ̃ and Assumption 2; reason: Assumption 1(b) for the policy
--   - encoding: B(1), G(1), conjugate symmetry → radial limits at 1; ψ(z̄) = conj ψ(z) on D; reason: §9.3 and p.22 conventions
-- source:
--   Caldentey–Giloni–Hurvich–Zhang, Information Design and Sharing in Supply Chains, SSRN 4319721 (v. 2024-01-20), https://ssrn.com/abstract=4319721, Lemma 6, p.39 (proof §9.14, pp.50–51)

import Mathlib
import Definitions.Def_InfoShareH2_Model
import Definitions.Def_InfoShareH2_Hardy

open Filter Topology MeasureTheory Complex

set_option autoImplicit false

namespace InfoShareH2

/-- **Lemma 6 (conjugate symmetry; normalization at `z = 1`).**
SSRN 4319721 (v. 2024-01-20), Lemma 6, p.39 (proof §9.14, pp.50–51). "For any function
`ψ̃(z) ∈ H²`, `ψ̃` is conjugate-symmetric if and only if `{ψ̃_k}` is real-valued. In addition, if
`ψ̃(z)` is conjugate-symmetric, its factors `B(z), G(z), Q(z)` defined in Lemma 2 are
conjugate-symmetric. Moreover, given Assumptions 1–2, we have `Q(1) := lim_{r→1−} Q(r) = 1`, and
`Q(e^{iλ})` is continuous at `λ = 0`. The inner function `M(z) = B(z)G(z)` satisfies
`B(1) = G(1) = 1`."

**Formalization Note** (corrected) Conjugate symmetry is `ψ̃(z̄) = \overline{ψ̃(z)}` on `D` (§9.3). The
factors are those of Lemma 2 (`Q` the outer part, `G` with constant `1`, the unimodular constant in
`B`); the second clause is for nonzero `ψ̃` (Lemma 2 factorizes nonzero functions only). "Given
Assumptions 1–2" is `ψ̃ ∈ Ψ̃` with Assumption 2. `B(1)` and `G(1)` are radial limits at `1`.

The clause "`Q(e^{iλ})` is continuous at `λ = 0`" is false for the boundary function of `Q` on `T`.
Take `Q = exp Θ`, `B = G = 1`, with `Θ = ∑_k [h_k − h_k(1) + \overline{h_k(z̄)} − \overline{h_k(1)}]`,
`h_k(z) = (1 − ρ_k)/(1 − ρ_k e^{−iλ_k} z)`, `λ_k = 2^{−k}`, and `ρ_k ↑ 1` fast enough that
`∑ √(1 − ρ_k)/λ_k < ∞`. Then `Q ∈ Ψ̃`, `(θ_n) ∈ ℓ²`, `Q` is analytic across `T ∖ {1}`, yet
`Q(e^{iλ_k})` stays near `e` as `λ_k → 0`. The clause is therefore replaced by the limit in the
Stolz regions of Definition 6, which §9.4 introduces for this purpose: `Q(z) → 1` as `z → 1` inside
each `R(K)`. -/
theorem lemma_6 :
    (∀ a ∈ H2, IsConjSymm (zTransform a) ↔ ∀ k, (a k).im = 0) ∧
    (∀ a ∈ H2, a ≠ 0 → IsConjSymm (zTransform a) →
      ∀ (B : BlaschkeData) (G : SingularData), G.c = 1 →
        (∀ z ∈ Disk, zTransform a z = outerPart a z * B.eval z * G.eval z) →
        IsConjSymm B.eval ∧ IsConjSymm G.eval ∧ IsConjSymm (outerPart a)) ∧
    (∀ ψ ∈ PsiTilde, Assumption2 ψ →
      ∀ (B : BlaschkeData) (G : SingularData), G.c = 1 →
        (∀ z ∈ Disk,
          zTransform (ofRealSeq ψ) z = outerPart (ofRealSeq ψ) z * B.eval z * G.eval z) →
        Tendsto (fun r : ℝ => outerPart (ofRealSeq ψ) r) (𝓝[<] (1 : ℝ)) (𝓝 1) ∧
        (∀ K : ℝ, Tendsto (outerPart (ofRealSeq ψ)) (𝓝[StolzRegion K] (1 : ℂ)) (𝓝 1)) ∧
        Tendsto (fun r : ℝ => B.eval r) (𝓝[<] (1 : ℝ)) (𝓝 1) ∧
        Tendsto (fun r : ℝ => G.eval r) (𝓝[<] (1 : ℝ)) (𝓝 1)) := by sorry

end InfoShareH2

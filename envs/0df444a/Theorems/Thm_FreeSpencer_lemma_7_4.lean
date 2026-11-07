-- Prove2me | Theorems.Thm_FreeSpencer_lemma_7_4
-- name    : FreeSpencer.lemma_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:06:41.178204+00:00
-- url     : https://prove2.me/theorems/15982a4e-a776-4e02-900a-b18e1830d611
-- title:
--   Lemma 7.4, p.51 — the Bellman residual of a tangent move
-- statement:
--   Let $u_1,\dots,u_k$ ($k>0$) be an orthonormal basis of $W$, $Q=\frac12P_W\preceq C\preceq I_\ell$, with $W$ vanishing on the frozen coordinates and perpendicular to $x$, and let $\xi$ be uniform on the $2k$ vectors $\pm\sqrt{k/2}\,u_j$. Then $\mathbb E\xi=0$, $\mathbb E\xi\xi^T=Q$, $\|\xi\|_2^2=k/2=\mathrm{Tr}\,Q$, $\xi\in\mathrm{ran}\,Q$. For $0<h<1$, $C-h^2Q$ has the range of $C$, and for every sample
--   $$\|x+h\xi\|_2^2-\|x\|_2^2=h^2\mathrm{Tr}\,Q=\mathrm{Tr}(C-(C-h^2Q)).$$
--   If $h\sqrt{k/2}$ is at most the distance of the live coordinates to the faces, the move stays in the cube and fixes the frozen coordinates. If $|e_\xi^{(4)}(s)|\le M_4$ for $|s|\le h$, with $e_\xi(s)=E(H+s\hat A(\xi),C-s^2Q)$, then
--   $$\Bigl|\mathbb EE(H+h\hat A(\xi),C-h^2Q)-E(H,C)-h^2\mathrm{Tr}\,Q(J-\Gamma)\Bigr|\le M_4h^4/24.$$
--   This holds for either potential.
--
--   Differences from the source:
--   - generalization: the block matrices Âᵢ = diag(Aᵢ, −Aᵢ) → any real symmetric contractions on a finite index type ι; reason: the analysis uses nothing about the blocks (p.30); ι = Fin m ⊕ Fin m with liftFam is the source
--   - generalization: "For sufficiently small h" → explicitly 0 < h < 1, and h√(k/2) ≤ 1 − |xᵢ| on live coordinates for the cube clause; reason: C − h²Q ⪰ (1 − h²)C (p.51); every sufficiently small h satisfies these
--   - encoding: expectations under Sample(Q), Tr Q(J − Γ) → averages over Fin k × Bool, and ½Σⱼ(J(uⱼ, uⱼ) − Γ(uⱼ, uⱼ)); reason: the same finite law, and Q = ½Σⱼuⱼuⱼᵀ
--   - encoding: J, Γ as derivatives (5.3); Tr(CJ) = Σₐ J(C^{1/2}eₐ, C^{1/2}eₐ) (p.31) → iterated deriv along lines of the potential, and the sum over the columns of MatrixLewis.mpow (1/2) C; reason: the same quantities; smoothness is in lemma_5_1 and theorem_D_1
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 7.4, p.51; proof pp.51–52

import Mathlib
import Definitions.Def_FreeSpencer_covForm
import Definitions.Def_FreeSpencer_IsDensity
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- **Lemma 7.4** (The Bellman residual of a tangent move), for either potential.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 7.4, p.51; proof p.52.

**Formalization Note** `W` is the span of the orthonormal `u₁, …, u_k`, `Q = ½ P_W`, and `Sample(Q)` is
the uniform law on the `2k` vectors `ξ p = ±√(k/2) u_j`, with expectations written as averages.
`Tr(QJ) = ½ ∑ⱼ J(uⱼ, uⱼ)` and `Tr(QΓ) = ½ ∑ⱼ Γ(uⱼ, uⱼ)`. "Sufficiently small `h`" is made explicit:
(7.4), (7.5) and the range clause hold for `0 < h < 1` (`C - h²Q ⪰ (1-h²) C`, p.51), and the cube clause
whenever `h √(k/2)` is below the distance of the live coordinates to the faces. `F` is the frozen set. -/
theorem lemma_7_4 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {ℓ k : ℕ} (Ah : Fin ℓ → Matrix ι ι ℝ) (hAh : IsContrFam Ah)
    (q θ κ : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (hθ : 0 < θ) (hκ : 0 ≤ κ)
    (H : Matrix ι ι ℝ) (hH : H.IsSymm) (C Q : Matrix (Fin ℓ) (Fin ℓ) ℝ) (hC : IsCov C) (hk : 0 < k)
    (u : Fin k → Fin ℓ → ℝ) (hu : ∀ i j, u i ⬝ᵥ u j = if i = j then 1 else 0)
    (hQ : Q = (1 / 2 : ℝ) • ∑ j, Matrix.vecMulVec (u j) (u j)) (hQC : (C - Q).PosSemidef)
    (x : Fin ℓ → ℝ) (F : Finset (Fin ℓ)) (hF : ∀ j, ∀ i ∈ F, u j i = 0) (hx : ∀ j, u j ⬝ᵥ x = 0)
    (ξ : Fin k × Bool → Fin ℓ → ℝ)
    (hξ : ξ = fun p => ((if p.2 then 1 else -1 : ℝ) * Real.sqrt ((k : ℝ) / 2)) • u p.1) :
    (2 * (k : ℝ))⁻¹ • ∑ p, ξ p = 0 ∧
    (2 * (k : ℝ))⁻¹ • ∑ p, Matrix.vecMulVec (ξ p) (ξ p) = Q ∧
    (∀ p, ξ p ⬝ᵥ ξ p = (k : ℝ) / 2) ∧
    Matrix.trace Q = (k : ℝ) / 2 ∧
    (∀ p, InRan Q (ξ p)) ∧
    ∀ h : ℝ, 0 < h → h < 1 →
      (∀ w, InRan (C - h ^ 2 • Q) w ↔ InRan C w) ∧
      (∀ p, (x + h • ξ p) ⬝ᵥ (x + h • ξ p) - x ⬝ᵥ x = h ^ 2 * Matrix.trace Q ∧
        h ^ 2 * Matrix.trace Q = Matrix.trace (C - (C - h ^ 2 • Q))) ∧
      ((∀ i, |x i| ≤ 1) → (∀ i, i ∉ F → h * Real.sqrt ((k : ℝ) / 2) ≤ 1 - |x i|) →
        ∀ p i, |(x + h • ξ p) i| ≤ 1 ∧ (i ∈ F → (x + h • ξ p) i = x i)) ∧
      ∀ M4 : ℝ,
        (∀ p, ∀ s : ℝ, |s| ≤ h →
          |iteratedDeriv 4 (fun r : ℝ => pot q θ κ Ah (H + r • aHat Ah (ξ p)) (C - r ^ 2 • Q)) s| ≤ M4) →
        |(2 * (k : ℝ))⁻¹ * ∑ p, pot q θ κ Ah (H + h • aHat Ah (ξ p)) (C - h ^ 2 • Q) -
            pot q θ κ Ah H C -
            h ^ 2 * ((1 / 2) * ∑ j, halfCurv q θ κ Ah H C (u j) -
              (1 / 2) * ∑ j, covForm q θ κ Ah H C (u j) (u j))| ≤ M4 * h ^ 4 / 24 := by sorry

end FreeSpencer

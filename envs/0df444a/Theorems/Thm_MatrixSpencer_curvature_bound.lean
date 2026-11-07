-- Prove2me | Theorems.Thm_MatrixSpencer_curvature_bound
-- name    : MatrixSpencer.curvature_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:45.611878+00:00
-- url     : https://prove2.me/theorems/795563c3-e922-44b8-8101-93a807706d05
-- title:
--   Proof of Lemma 2.6, Steps 1–2, pp.28, 30 — regularity of $W$ and $[\Theta_{ij}(W)]\succeq\frac12I_n\otimes W$
-- statement:
--   Assume (2.2), and let $M_1,\dots,M_n\in\mathbb R^{d\times d}$ be symmetric with $\sum_iM_i^2\preceq\eta I$. Let $\Omega=\{g:\|B(g)\|<1\}$ and $W(g)=e^{-\|g\|_2^2/2-V(B(g))}(R\otimes R)$. Then $W$ is $C^\infty$ with positive definite values on $\Omega$, its entries are integrable on $\Omega$, and for all $g\in\Omega$ and $z_1,\dots,z_n\in\mathbb R^d\otimes\mathbb R^d$,
--
--   $$\sum_{i,j=1}^nz_i^\top\Theta_{ij}(W)z_j\ge\frac12\sum_{i=1}^nz_i^\top W z_i .$$
--
--   So $W$ satisfies the hypotheses of the matrix Poincaré inequality with $\lambda=1/2$.
--
--   Differences from the source:
--   - reading: M₁,…,Mₙ ∈ ℝ^{d×d} (no word "symmetric") → the Mᵢ are symmetric; reason: ⪯ and V(X) = Tr v(X) are defined for symmetric matrices only (p.6, p.8), and the only use of the statement has symmetric Mᵢ
--   - reading: Step 1 proves integrability of the trace and continuity; smoothness and positive definiteness of W are used by "the matrix-weighted Poincaré inequality" without a printed claim → the conclusion states C^∞ and PosDef on Ω and integrability of the entries; reason: these are the hypotheses of Lemma 2.1, which p.27 says are established; a positive matrix with integrable trace has integrable entries
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), proof of Lemma 2.6, p.27 (PDF p.29), Step 1, p.28 (PDF p.30), Step 2, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_MatrixSpencer_Param22
import Definitions.Def_MatrixSpencer_series
import Definitions.Def_MatrixSpencer_curvature
import Definitions.Def_MatrixSpencer_matWeight
open RBMSensitivity (E)
open Matrix
open scoped ContDiff
open scoped Matrix.Norms.L2Operator

namespace MatrixSpencer

/-- **Regularity and the block-curvature bound for `W`, proof of Lemma 2.6, Steps 1–2.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), proof of Lemma 2.6, p.27 (PDF p.29): "W(g) = e^{−‖g‖²₂/2−V(B(g))}(R ⊗ R)"; Step 1, p.28 (PDF p.30): "W has
integrable trace"; Step 2, p.30 (PDF p.32): "this proves the block-curvature bound [Θ̃_ij]ⁿᵢ,ⱼ₌₁ ⪰ ½I_{nd²}, or
equivalently [Θ_ij(W)]ⁿᵢ,ⱼ₌₁ ⪰ ½Iₙ ⊗ W."

**Formalization Note.** `Ω = {g : ‖B(g)‖ < 1}`, the domain on which p.27 applies Lemma 2.1. The conclusion
is exactly what `lemma_2_1` consumes at `lam = 1/2` with `ι = Fin d × Fin d`: positive definite and `C^∞` on
`Ω`, entries integrable on `Ω` (a positive matrix with integrable trace has integrable entries), and the
curvature form, stated in the shape of (A.1), for all `z₁, …, zₙ ∈ ℝ^d ⊗ ℝ^d`. The `Mᵢ` are symmetric, as
in `theorem_2_5`. -/
theorem curvature_bound {n d : ℕ} (α β : ℝ) (p : ℕ) (η : ℝ) (h : Param22 α β p η)
    (M : Fin n → Matrix (Fin d) (Fin d) ℝ) (hM : ∀ i, (M i).IsSymm)
    (hV : (η • (1 : Matrix (Fin d) (Fin d) ℝ) - ∑ i, M i ^ 2).PosSemidef) :
    let Ω : Set (E n) := {g | ‖series M g‖ < 1}
    let W := matWeight α β p M
    (∀ a b, ContDiffOn ℝ ∞ (fun g => W g a b) Ω) ∧
    (∀ a b, MeasureTheory.IntegrableOn (fun g => W g a b) Ω) ∧
    ∀ g ∈ Ω, (W g).PosDef ∧
      ∀ z : Fin n → (Fin d × Fin d → ℝ),
        (1 / 2 : ℝ) * ∑ i, z i ⬝ᵥ W g *ᵥ z i ≤ ∑ i, ∑ j, z i ⬝ᵥ curvature W i j g *ᵥ z j := by sorry

end MatrixSpencer

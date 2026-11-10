-- Prove2me | Theorems.Thm_IntLInfty_Kan_fillerAt_zero_abs
-- name    : IntLInfty.Kan.fillerAt_zero_abs
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:15:55.083204+00:00
-- url     : https://prove2.me/theorems/99c72335-a2f9-42d2-b807-c97986ac071f
-- title:
--   Horn-$0$ filler for $\int_r$ from abstract Volterra fibre data (Henriques, Thm 5.10 proof)
-- statement:
--   Let $\delta$ be an $L_\infty$-structure on $L$ and $S'\le S$ generating systems. Suppose the integrality conditions in the ambient Banach spaces $A_{m+1}=\mathrm{Amb}_r(S,m+1)$ and $A_m$ are cut out as $z\in\int_r \iff H(z-G(z))=0$ by smooth maps $G_1,G_0$ and idempotent continuous linear maps $H_1,H_0$ compatible with the faces $d_i$ ($i\neq0$); suppose $G_1,G_0$ are affine along the images of idempotents $\pi_1,\pi_0$ that their derivatives preserve, with $\|(DG)^n\|<1$ for some $n$ (Volterra condition), $\pi$ compatible with faces and killed by restriction, and $H_1(z-G_1z)\in\operatorname{im}\pi_1$ whenever $\operatorname{res} z$ is integral; and let $Z$ be a smooth family of (non-integral) horn fillers extending horn data and fixing $\Lambda^0$-restrictions of each point. Then there is a smooth family $\sigma$ of fillers for the relative horn $\Lambda^{m+1}_0$: for integral $x$ and integral relative-horn data $y$,
--
--   $$\sigma(x,y)\in{\textstyle\int_r},\qquad \mathrm{kan}(\sigma(x,y))=y,\qquad \sigma(x,\mathrm{kan}(x))=x.$$
--
--   Role: the abstract horn-$0$ filling step of the Kan-fibration argument in the proof of Theorem 5.10; the parent instantiates it with its concrete Volterra map $G$, projector $H$ and radial filler $Z$, so the filler construction is checked once over abstract data.
--
--   **Formalization Note**: all fibre data are explicit arguments with their facts as hypotheses, so the statement uses only the Definitions bundle.
-- source:
--   Henriques, Integrating L-infinity algebras, arXiv:math/0603563v2, proof of Theorem 5.10, p. 16 (horn filling via the inverse function theorem on the fibre)

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ
open scoped ContDiff

namespace IntLInfty.Kan

theorem fillerAt_zero_abs {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, _root_.Module ℝ (L i)]
    [∀ i, FiniteDimensional ℝ (L i)] {r m : ℕ} (δ : LInfty L) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    [CompleteSpace (Amb r S (m + 1))] [CompleteSpace (Amb r S m)]
    (G1 : Amb r S (m + 1) → Amb r S (m + 1)) (G0 : Amb r S m → Amb r S m)
    (H1 : Amb r S (m + 1) →L[ℝ] Amb r S (m + 1)) (H0 : Amb r S m →L[ℝ] Amb r S m)
    (Z : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ 0} → Amb r S m) × Amb r S' (m + 1)) →
      Amb r S (m + 1))
    (hG1 : ContDiff ℝ ∞ G1)
    (hV1 : ∀ x, ∃ n : ℕ, ‖(fderiv ℝ G1 x) ^ n‖ < 1)
    (hV0 : ∀ x, ∃ n : ℕ, ‖(fderiv ℝ G0 x) ^ n‖ < 1)
    (hGf : ∀ i : Fin (m + 2), i ≠ 0 → ∀ z, faceAmb r S m i (G1 z) = G0 (faceAmb r S m i z))
    (hint1 : ∀ z, z ∈ integ r δ S (m + 1) ↔ H1 (z - G1 z) = 0)
    (hint0 : ∀ z, z ∈ integ r δ S m ↔ H0 (z - G0 z) = 0)
    (hHid : ∀ z, H1 (H1 z) = H1 z)
    (hHf : ∀ i : Fin (m + 2), i ≠ 0 → ∀ z, faceAmb r S m i (H1 z) = H0 (faceAmb r S m i z))
    (hFsub : ∀ (i : Fin (m + 2)) (a b : Amb r S (m + 1)),
      faceAmb r S m i (a - b) = faceAmb r S m i a - faceAmb r S m i b)
    (hRsub : ∀ a b : Amb r S (m + 1), res h (a - b) = res h a - res h b)
    (hZc : ∀ x, ContDiff ℝ ∞ (fun y => Z x y))
    (hZres : ∀ x y, res h (Z x y) = y.2)
    (hZface : ∀ x (y : ({i : Fin (m + 2) // i ≠ 0} → Amb r S m) × Amb r S' (m + 1)),
      HornCompat (fun q => faceAmb r S q) m 0 y.1 →
      (∀ i, faceAmb r S' m i.1 y.2 = res h (y.1 i)) → ∀ i, faceAmb r S m i.1 (Z x y) = y.1 i)
    (hZkan : ∀ x, Z x (kanMap h m 0 x) = x)
    (π1 : Amb r S (m + 1) →L[ℝ] Amb r S (m + 1)) (π0 : Amb r S m →L[ℝ] Amb r S m)
    (hπ1 : ∀ x, π1 (π1 x) = π1 x) (hπ0 : ∀ x, π0 (π0 x) = π0 x)
    (hI1 : ∀ z v, π1 v = v → π1 (fderiv ℝ G1 z v) = fderiv ℝ G1 z v)
    (hI0 : ∀ z v, π0 v = v → π0 (fderiv ℝ G0 z v) = fderiv ℝ G0 z v)
    (hA1 : ∀ z v, π1 v = v → G1 (z + v) = G1 z + fderiv ℝ G1 z v)
    (hA0 : ∀ z v, π0 v = v → G0 (z + v) = G0 z + fderiv ℝ G0 z v)
    (hface : ∀ i : Fin (m + 2), i ≠ 0 → ∀ v, π1 v = v → π0 (faceAmb r S m i v) = faceAmb r S m i v)
    (hres : ∀ v, π1 v = v → res h v = 0)
    (hu : ∀ z0 : Amb r S (m + 1), res h z0 ∈ integ r δ S' (m + 1) →
      π1 (H1 (z0 - G1 z0)) = H1 (z0 - G1 z0)) :
    ∃ σ : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ 0} → Amb r S m) × Amb r S' (m + 1)) →
        Amb r S (m + 1),
      (∀ x, ContDiff ℝ ∞ (σ x)) ∧
      (∀ x ∈ integ r δ S (m + 1), ∀ y ∈ RelHorn r δ h m 0,
          σ x y ∈ integ r δ S (m + 1) ∧ kanMap h m 0 (σ x y) = y) ∧
      (∀ x ∈ integ r δ S (m + 1), σ x (kanMap h m 0 x) = x) := by sorry

end IntLInfty.Kan

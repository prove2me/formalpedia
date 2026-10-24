-- Prove2me | Theorems.Thm_MICPRep_Periodic_lemma_6_4
-- name    : MICPRep.Periodic.lemma_6_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:13.316427+00:00
-- url     : https://prove2.me/theorems/0a3d7a0a-f3df-4bf8-934c-7a44731fe35b
-- title:
--   Lemma 6.4 (with F ∩ ℤᵈ ≠ ∅ added), p. 25 — a unimodular U maps a rational affine subspace onto ℝᵏ × {0}ᵈ⁻ᵏ
-- statement:
--   Let $F \subseteq \mathbb R^d$ be a rational affine subspace of dimension $k$ that contains an integer point, and let $L = F - z$ ($z \in F$) be its direction. Then there are $c \in \mathbb Z^d \cap F$ and a unimodular $U \in \mathbb Z^{d\times d}$ with
--   $$UL = U(F - c) = \mathbb R^k \times \{0\}^{d-k}, \qquad (U^{\mathsf T})^{-1}L^\perp = \{0\}^k \times \mathbb R^{d-k}.$$
--   Furthermore, if $F = r\mathbb R$ for some $r \in \mathbb Z^d\setminus\{0\}$ with $\gcd(r_1,\dots,r_d) = 1$, then $c$ and $U$ can be chosen so that in addition $U^{-1}e(1) = r$.
--
--   This is the standard alignment of a lattice subspace with a coordinate subspace by a lattice-preserving change of basis; Lemmas 6.5, 6.11 and 6.12 use it.
--
--   **Formalization Note** The hypothesis $F \cap \mathbb Z^d \neq \emptyset$ is added: as printed the lemma fails for $F = \{z : z_1 = 1/2\}$, a rational affine subspace without integer points, and every use in the paper has one. Unimodular means a unit of the integer matrix ring (Definition 6.4). $L^\perp$ is taken with the dot product, $e(1)$ is the unit vector of the coordinate with $0$-based index $0$, and $\gcd$ is `Finset.univ.gcd`.
-- source:
--   Lubin, Vielma, Zadik, Mixed-integer convex representability, arXiv:1706.05135v3, p. 25, Lemma 6.4 (with the hypothesis F ∩ ℤᵈ ≠ ∅ added)

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

namespace MICPRep.Periodic

open scoped ENNReal Matrix

/-- Lemma 6.4, p. 25, with `F ∩ ℤᵈ ≠ ∅` added. -/
theorem lemma_6_4 {d k : ℕ} (F : AffineSubspace ℝ (Fin d → ℝ))
    (hF : IsRationalAffineSubspace F) (hdim : affDim F = (k : ℤ))
    (hFZ : ((F : Set (Fin d → ℝ)) ∩ intLattice d).Nonempty) :
    (∃ c ∈ intLattice d ∩ (F : Set (Fin d → ℝ)), ∃ U : Matrix (Fin d) (Fin d) ℤ,
      IsUnimodular U ∧
      intMatVec U '' (F.direction : Set (Fin d → ℝ)) = coordSubspace d k ∧
      (fun z => intMatVec U (z - c)) '' (F : Set (Fin d → ℝ)) = coordSubspace d k ∧
      (fun w => ((U.map (fun m : ℤ => (m : ℝ)))ᵀ)⁻¹ *ᵥ w) ''
          {w : Fin d → ℝ | ∀ v ∈ F.direction, w ⬝ᵥ v = 0} =
        {z : Fin d → ℝ | ∀ i : Fin d, (i.val : ℤ) < k → z i = 0}) ∧
    ∀ r : Fin d → ℤ, r ≠ 0 → Finset.univ.gcd r = 1 →
      (F : Set (Fin d → ℝ)) = {z | ∃ t : ℝ, z = t • (fun i => (r i : ℝ))} →
      ∃ c ∈ intLattice d ∩ (F : Set (Fin d → ℝ)), ∃ U : Matrix (Fin d) (Fin d) ℤ,
        IsUnimodular U ∧
        intMatVec U '' (F.direction : Set (Fin d → ℝ)) = coordSubspace d k ∧
        (fun z => intMatVec U (z - c)) '' (F : Set (Fin d → ℝ)) = coordSubspace d k ∧
        (fun w => ((U.map (fun m : ℤ => (m : ℝ)))ᵀ)⁻¹ *ᵥ w) ''
            {w : Fin d → ℝ | ∀ v ∈ F.direction, w ⬝ᵥ v = 0} =
          {z : Fin d → ℝ | ∀ i : Fin d, (i.val : ℤ) < k → z i = 0} ∧
        ∀ i : Fin d, i.val = 0 →
          (U.map (fun m : ℤ => (m : ℝ)))⁻¹ *ᵥ Pi.single i 1 = fun j => (r j : ℝ) := by sorry

end MICPRep.Periodic

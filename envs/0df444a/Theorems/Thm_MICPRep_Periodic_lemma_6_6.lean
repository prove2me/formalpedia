-- Prove2me | Theorems.Thm_MICPRep_Periodic_lemma_6_6
-- name    : MICPRep.Periodic.lemma_6_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:11.455077+00:00
-- url     : https://prove2.me/theorems/f0645fbe-80ae-41da-81f7-6d3e9822f945
-- title:
--   Lemma 6.6, p. 25 — a rational affine change of the integer variables keeps a rational MICP formulation and does not increase D_MICP
-- statement:
--   Let $M \subseteq \mathbb R^{n+p+d}$ be closed and convex such that $(M, d)$ induces a rational MICP formulation of $S \subseteq \mathbb R^n$ with index set $I$ and $z$-projected sets $\{A_z\}$. Let $R : \mathbb R^d \to \mathbb R^d$ be an invertible rational affine map with $R^{-1}(\mathbb Z^d) \subseteq \mathbb Z^d$, and
--   $$M' = \{(x, y, z) : (x, y, R^{-1}(z)) \in M\}.$$
--   Then $M'$ is closed and convex, $(M', d)$ induces a rational MICP formulation of
--   $$S' = \bigcup_{z' \in R(I) \cap \mathbb Z^d} A_{R^{-1}(z')}$$
--   with index set $I' = R(I)$, and $D_{\mathrm{MICP}}(M') \le D_{\mathrm{MICP}}(M)$. If in addition $R(\mathbb Z^d) = R^{-1}(\mathbb Z^d) = \mathbb Z^d$, then $S' = S$ and $D_{\mathrm{MICP}}(M) = D_{\mathrm{MICP}}(M')$.
--
--   The lemma lets the proof rearrange the index set by unimodular and slicing maps without loss of generality.
--
--   **Formalization Note** $R = $ `ratAff A b` with $A$ invertible and $R^{-1} = $ `ratAffInv A b`; $R^{-1}(\mathbb Z^d)$ is written as the preimage of $\mathbb Z^d$ under $R$.
-- source:
--   Lubin, Vielma, Zadik, Mixed-integer convex representability, arXiv:1706.05135v3, p. 25, Lemma 6.6

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

namespace MICPRep.Periodic

open scoped ENNReal Matrix

/-- Lemma 6.6, p. 25. -/
theorem lemma_6_6 {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ)
    (hA : IsUnit A) (hpre : ratAff A b ⁻¹' intLattice d ⊆ intLattice d) :
    let M' : Set (Ambient n p d) := {q | (q.1, q.2.1, ratAffInv A b q.2.2) ∈ M}
    let S' : Set (Pt n) :=
      ⋃ z' ∈ ratAff A b '' indexSet M ∩ intLattice d, zProj M (ratAffInv A b z')
    IsRationalFormulation M' S' ∧ indexSet M' = ratAff A b '' indexSet M ∧
      micpDiam M' ≤ micpDiam M ∧
      (ratAff A b '' intLattice d = intLattice d →
        ratAff A b ⁻¹' intLattice d = intLattice d →
        S' = S ∧ micpDiam M = micpDiam M') := by sorry

end MICPRep.Periodic

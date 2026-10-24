-- Prove2me | Theorems.Thm_MICPRep_Periodic_lemma_6_12
-- name    : MICPRep.Periodic.lemma_6_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:25.088273+00:00
-- url     : https://prove2.me/theorems/c4239902-4e6a-4b06-b98a-8e3524bb8f8b
-- title:
--   Lemma 6.12 (integer indices of the new formulation), pp. 29–30 — relaxing integrality along an integer recession direction r of I
-- statement:
--   Let $M \subseteq \mathbb R^{n+p+d}$ be closed and convex such that $(M, d)$ induces a rational MICP formulation with index set $I$ and $z$-projected sets $\{A_z\}$, and let $r \in (\mathbb Z^d \cap I_\infty) \setminus \{0\}$. Then there is a closed convex $\tilde M \subseteq \mathbb R^{n + (p+1) + (d-1)}$ such that $(\tilde M, d-1)$ induces a rational MICP formulation of some set, and a set $\tilde A$ is a $z$-projected set $\tilde A_{\tilde z}$ of that formulation at an integer index $\tilde z \in \tilde I \cap \mathbb Z^{d-1}$ if and only if there is $z^0 \in \mathbb Z^d \cap I$ with
--   $$\tilde A = \bigcup_{z' \in (z^0 + r\mathbb R) \cap I} A_{z'}.$$
--   In particular, $\bigcup_{z' \in (z^0 + r\mathbb R)\cap I} A_{z'}$ is convex for every $z^0 \in \mathbb Z^d \cap I$.
--
--   The lemma trades one integer variable for one continuous variable along a recession direction; it is the reduction step (c) of Lemma 6.2.
--
--   **Formalization Note** $d$ is written $d' + 1$ ($r \ne 0$ forces $d \ge 1$). The paper's "$\tilde A$ is a $z$-projected set of the formulation" is read at integer indices $\tilde z \in \tilde I \cap \mathbb Z^{d-1}$: these are the only $z$-projected sets entering the represented set and the only ones Lemma 6.2 uses; at a non-integer $\tilde z$ the corresponding line contains no integer point and the "only if" direction fails in general.
-- source:
--   Lubin, Vielma, Zadik, Mixed-integer convex representability, arXiv:1706.05135v3, pp. 29–30, Lemma 6.12 (z-projected sets of the new formulation read at integer indices)

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

namespace MICPRep.Periodic

open scoped ENNReal Matrix

/-- Lemma 6.12, pp. 29–30 (z-projected sets of the new formulation read at integer indices). -/
theorem lemma_6_12 {n p d' : ℕ} (M : Set (Ambient n p (d' + 1))) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (r : Fin (d' + 1) → ℝ)
    (hrZ : r ∈ intLattice (d' + 1)) (hrI : r ∈ recCone (indexSet M)) (hr0 : r ≠ 0) :
    ∃ (Mt : Set (Ambient n (p + 1) d')) (St : Set (Pt n)), IsRationalFormulation Mt St ∧
      (∀ At : Set (Pt n),
        (∃ zt ∈ indexSet Mt ∩ intLattice d', At = zProj Mt zt) ↔
          ∃ z₀ ∈ intLattice (d' + 1) ∩ indexSet M,
            At = ⋃ z' ∈ {z | ∃ t : ℝ, z = z₀ + t • r} ∩ indexSet M, zProj M z') ∧
      ∀ z₀ ∈ intLattice (d' + 1) ∩ indexSet M,
        Convex ℝ (⋃ z' ∈ {z | ∃ t : ℝ, z = z₀ + t • r} ∩ indexSet M, zProj M z') := by sorry

end MICPRep.Periodic

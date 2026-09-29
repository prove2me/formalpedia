-- Prove2me | Theorems.Thm_GrapheneTightBinding_massiveDiracHam_charpoly_and_gap
-- name    : GrapheneTightBinding.massiveDiracHam_charpoly_and_gap
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:27:48.5057+00:00
-- url     : https://prove2.me/theorems/95540e52-91c3-4f13-8949-68aea3a037e3
-- title:
--   Eqs. (33)–(34): the $\sigma_z$ mass term opens a gap $2v_F|M|$
-- statement:
--   **The mass term gaps the cone (Eqs. 33–34).** Let $a>0$, $t>0$ and $M\neq0$. The massive
--   Dirac Hamiltonian $h_M(q)=v_F(q_x\sigma_x+q_y\sigma_y+M\sigma_z)$ has characteristic
--   polynomial $X^2-v_F^2(q_x^2+q_y^2+M^2)$, i.e. eigenvalues
--   $$E_{M,\pm}(q)=\pm v_F\sqrt{q_x^2+q_y^2+M^2},$$
--   and these are bounded away from zero: $v_F|M|>0$ and $E_{M,+}(q)\ge v_F|M|$ for every
--   $q$, so the spectrum has a gap of width $2v_F|M|$ and the Dirac cone of Eq. (32) is
--   destroyed. Physically this is what happens when the $A$ and $B$ sites carry different
--   on-site energies, as in boron nitride.
--
--   *Note on the source.* Eq. (34) of the source is written
--   $E_{M,\pm}=\pm\sqrt{q_x^2+q_y^2+M^2}$, omitting the overall factor $v_F$ that is present
--   in its own Eq. (33); the statement formalised here keeps that factor.
-- source:
--   Franz Utermohlen, Tight-Binding Model for Graphene, lecture notes, September 12, 2018 (Ohio State University); equation numbers as in that text.

import Definitions.Def_graphene_tb_hamiltonian

open Asymptotics Polynomial

namespace GrapheneTightBinding

theorem massiveDiracHam_charpoly_and_gap (a t M : ℝ) (ha : 0 < a) (ht : 0 < t) (hM : M ≠ 0) :
    (∀ q : ℝ × ℝ, (massiveDiracHam a t M q).charpoly =
        X ^ 2 - C ((fermiVel a t ^ 2 * (q.1 ^ 2 + q.2 ^ 2 + M ^ 2) : ℝ) : ℂ)) ∧
      0 < fermiVel a t * |M| ∧
      ∀ q : ℝ × ℝ, fermiVel a t * |M|
        ≤ fermiVel a t * Real.sqrt (q.1 ^ 2 + q.2 ^ 2 + M ^ 2) := by
  sorry

end GrapheneTightBinding

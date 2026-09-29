-- Prove2me | Theorems.Thm_GallegoOzerADI_PositiveSetup_V_abConvex_coercive
-- name    : GallegoOzerADI.PositiveSetup.V_abConvex_coercive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:50:13.93352+00:00
-- url     : https://prove2.me/theorems/29bdb8b7-d22a-428c-9313-a8fe1e1d1ff9
-- title:
--   Theorem 1, Part 1 — $V_t(\cdot, o_t) \in C(0, K_t)$ and $V_t(x, o_t) \to \infty$ as $|x| \to \infty$
-- statement:
--   Consider the finite-horizon inventory model with advance demand information and set-up costs (Definition `Model`, the functional equation (8)–(9)), with $N > L+1$. For every period $1 \le t \le T$ and every fixed vector $o_t \in \mathbb{R}^{M}$ of observed demands beyond the protection period,
--
--   $$
--   V_t(\cdot, o_t) \in C(0, K_t) \qquad\text{and}\qquad \lim_{|x| \to \infty} V_t(x, o_t) = \infty.
--   $$
--
--   The cost-to-go after ordering is $K_t$-convex in the order-up-to level and coercive, whatever advance demand information has been observed. This is the induction hypothesis of the paper's proof of the $(s,S)$ structure: it yields a finite minimizer of $V_t(\cdot, o_t)$ and the conditions of Lemma 2.
--
--   **Formalization Note** $\lim_{|x|\to\infty}$ is the limit along the cocompact filter of $\mathbb{R}$. The vector $o_t$ is arbitrary, with no sign restriction. The standing hypotheses are those of the `Model` definition.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1350, Theorem 1, Part 1 (proof p. 1356)

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model

open Filter

namespace GallegoOzerADI.PositiveSetup

theorem V_abConvex_coercive {L M : ℕ} [NeZero M] (P : Model L M) (t : ℕ) (ht₁ : 1 ≤ t)
    (htT : t ≤ P.T) (o : Fin M → ℝ) :
    ABConvex 0 (P.K t) (fun y => P.V t y o) ∧
      Tendsto (fun y => P.V t y o) (cocompact ℝ) atTop := by sorry

end GallegoOzerADI.PositiveSetup

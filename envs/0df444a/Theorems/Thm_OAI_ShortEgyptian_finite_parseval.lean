-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_finite_parseval
-- name    : OAI.ShortEgyptian.finite_parseval
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:17:38.856559+00:00
-- url     : https://prove2.me/theorems/b410ac31-660d-41c5-b4dd-eaf1532d1f04
-- title:
--   Parseval identity for the additive characters of $\mathbb{Z}/q\mathbb{Z}$
-- statement:
--   Let $q\ge1$ be an integer and let $e_q:\mathbb{Z}/q\mathbb{Z}\to\mathbb{C}$ be the standard additive character, $e_q(x)=\exp(2\pi i x/q)$, which is well defined on residue classes. For every function $\beta:\mathbb{Z}/q\mathbb{Z}\to\mathbb{C}$,
--
--   $$
--   \sum_{x\in\mathbb{Z}/q\mathbb{Z}}\Big|\sum_{y\in\mathbb{Z}/q\mathbb{Z}}\beta(y)\,e_q(xy)\Big|^2=q\sum_{y\in\mathbb{Z}/q\mathbb{Z}}|\beta(y)|^2 .
--   $$
--
--   This is the Parseval (Plancherel) identity for the discrete Fourier transform on the cyclic group of order $q$. Applied to the indicator function of a set $A$ of residues it gives $\sum_{k}\big|\sum_{a\in A}e_q(ka)\big|^2=q|A|$, the basic $L^2$ input for discrepancy estimates that bound how many frequencies can carry a large character sum.
--
--   **Formalization Note** The modulus is a natural number `q` with `NeZero q`, the group is `ZMod q`, the character $e_q$ is `ZMod.stdAddChar`, and $|\cdot|$ is the complex norm.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/FiniteFourier.lean#L18-L41

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic

open OAI OAI.ShortEgyptian
universe uι uG
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.finite_parseval {q : ℕ} [NeZero q] (β : ZMod q → ℂ) :
    ∑ x : ZMod q, ‖∑ y : ZMod q, β y * ZMod.stdAddChar (x * y)‖ ^ 2 =
      (q : ℝ) * ∑ y : ZMod q, ‖β y‖ ^ 2 := by sorry

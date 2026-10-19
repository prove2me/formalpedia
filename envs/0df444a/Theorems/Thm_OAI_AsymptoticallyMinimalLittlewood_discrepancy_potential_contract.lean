-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_discrepancy_potential_contract
-- name    : OAI.AsymptoticallyMinimalLittlewood.discrepancy_potential_contract
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:45:23.522282+00:00
-- url     : https://prove2.me/theorems/872e9b37-e4b9-4b1b-b520-78747610acad
-- title:
--   Contraction of the potential $\sqrt{u\log(16R/u)}$ when $u\le\tfrac{15}{16}s$
-- statement:
--   Let $s,u,R$ be real numbers with $0<s\le R$ and $0\le u\le\tfrac{15}{16}s$. Then
--
--   $$
--   \sqrt{u\log\frac{16R}{u}}\le\frac{63}{64}\sqrt{s\log\frac{16R}{s}}.
--   $$
--
--   The function $\Phi(s)=\sqrt{s\log(16R/s)}$ is the discrepancy scale for a matrix with $R$ rows and $s$ remaining columns. The inequality says that when a partial-coloring step removes at least a $1/16$ fraction of the columns, this potential drops by the factor $63/64$, so the errors of the successive steps form a convergent geometric series.
--
--   **Formalization Note** For $u=0$ the left side is $\sqrt{0\cdot\log(16R/0)}=0$ (in Lean $16R/0=0$ and $\log0=0$, but the product is $0$ regardless).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L586-L628

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.discrepancy_potential_contract {s u R : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (hu0 : 0 ≤ u) (hu : u ≤ (15 / 16) * s) :
    Real.sqrt (u * Real.log (16 * R / u)) ≤
      (63 / 64) * Real.sqrt (s * Real.log (16 * R / s)) := by sorry

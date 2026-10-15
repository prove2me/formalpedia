-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_exists_energy_parameters
-- name    : OAI.DoublingHilbert.exists_energy_parameters
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:40:27.953099+00:00
-- url     : https://prove2.me/theorems/9c8d475d-7381-446d-9dfb-2077fce309ff
-- title:
--   Choosing the width factor and the accuracy that make the anisotropic energy bound smaller than $\eta$
-- statement:
--   For real numbers $D$ and $C$ let
--   $c_h(D)=4+8D(2D+1)$ and $c_v(D,C)=4+2C+8CD+8D(2D+1)$
--   be the horizontal and vertical energy coefficients. For all real numbers $D\ge0$, $C\ge0$ and $\eta>0$ there exist an integer $W\ge1$ and a real number $t$ with $0<t\le1$ such that
--
--   $$
--   2\cdot\frac{\eta}{8}+\frac{16\,C\,D^2}{W}+\big(W^2\,c_h(D)+c_v(D,C)\big)\,t<\eta .
--   $$
--
--   The left-hand side is the bound on the average combined energy $W^2\,\mathbb{E}[\mathcal{E}^h]+\mathbb{E}[\mathcal{E}^v]$ that the anisotropic energy estimates give with barrier slack $\varepsilon=\eta/8$, width factor $W$ and accuracy $t$. The order of the choices is essential: $W$ is chosen first, depending on the barrier constant $C$, to make $16CD^2/W$ small, and only afterwards $t$ is chosen small depending on $W$, because the horizontal coefficient is multiplied by $W^2$.
--
--   **Formalization Note** $W$ is a natural number with $0<W$, cast to $\mathbb{R}$; $c_h$ and $c_v$ are `horizontalCoefficient D` and `verticalCoefficient D C`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Energy.lean#L295-L322

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy

open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter

theorem OAI.DoublingHilbert.exists_energy_parameters {D C η : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ W : ℕ, 0 < W ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      2 * (η / 8) + 16 * C * D ^ 2 / (W : ℝ) +
        ((W : ℝ) ^ 2 * horizontalCoefficient D + verticalCoefficient D C) * t < η := by sorry

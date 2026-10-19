-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_nibble_parameters
-- name    : OAI.AsymptoticallyMinimalLittlewood.Nibble.nibble_parameters
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:21:09.296299+00:00
-- url     : https://prove2.me/theorems/7a104fec-cad2-46d5-9916-7d19f2b524f6
-- title:
--   Existence of step size, number of rounds and tolerance for the nibble iteration
-- statement:
--   For every natural number $r$ and every real number $d>0$ there exist a real number $a$, a natural number $k$ and a real number $e_0$ such that, writing $q=1-(r-1)a$,
--
--   $$
--   0<a\le\frac1{16},\qquad ra\le\frac14,\qquad e_0>0,\qquad q^k>0,
--   $$
--   $$
--   (1+2ra)^k\big(e_0+8r^2a^2k\big)\le\frac{q^k}{4},\qquad\Big(1-\frac a2\Big)^k\le d,\qquad k\,(16r+1)\,a^2\le d.
--   $$
--
--   These are the scale-free forms of the parameter hypotheses of the nibble iteration: for an initial degree $D$ and irregularity $\varepsilon=e_0D$, the degree error accumulated over $k$ rounds stays below a quarter of the current degree $q^kD$, the active vertex set shrinks below a $d$-fraction, and the total waste is at most a $d$-fraction. The numbers $a$, $k$ and $e_0$ depend only on $r$ and $d$.
--
--   **Formalization Note** The factor $r-1$ is the natural-number subtraction `r - 1` cast to the reals, so for $r=0$ it equals $0$ (and $q=1$); no lower bound on $r$ is assumed. In the Lean statement the parameter $e_0$ is called `e`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Nibble.lean#L920-L989

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Nibble
universe uI uE uV
open scoped BigOperators
open Finset
variable {V : Type uV} {E : Type uE} [DecidableEq V] [Fintype E] [DecidableEq E]
open Filter Topology

theorem OAI.AsymptoticallyMinimalLittlewood.Nibble.nibble_parameters (r : ℕ) {d : ℝ} (hd : 0 < d) :
    ∃ (a : ℝ) (k : ℕ) (e : ℝ), 0 < a ∧ a ≤ 1/16 ∧
      (r : ℝ)*a ≤ 1/4 ∧ 0 < e ∧
      0 < (1-((r-1 : ℕ) : ℝ)*a)^k ∧
      (1+2*(r : ℝ)*a)^k*(e+8*(r : ℝ)^2*a^2*k) ≤
        (1-((r-1 : ℕ) : ℝ)*a)^k/4 ∧
      (1-a/2)^k ≤ d ∧ k*(16*(r : ℝ)+1)*a^2 ≤ d := by sorry

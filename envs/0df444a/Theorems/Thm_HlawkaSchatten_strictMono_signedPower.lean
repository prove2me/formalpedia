-- Prove2me | Theorems.Thm_HlawkaSchatten_strictMono_signedPower
-- name    : HlawkaSchatten.strictMono_signedPower
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T06:53:31.575019+00:00
-- url     : https://prove2.me/theorems/40d0875c-f4fd-460a-a9d9-884730d5aa86
-- title:
--   The signed power $x \mapsto \operatorname{sgn}(x)|x|^{q}$ is strictly increasing for every exponent $q>0$
-- statement:
--   Let $q \in \mathbb R$ with $q>0$. For $x \in \mathbb R$ write $\mathrm{signedPower}(q,x)=\operatorname{sgn}(x)\,|x|^{q}$ (with $\operatorname{sgn}(0)=0$). Then
--
--   $$
--   \mathrm{signedPower}(q,\cdot) \text{ is strictly monotone on } \mathbb R,
--   $$
--
--   that is, $x<y$ implies $\operatorname{sgn}(x)|x|^{q}<\operatorname{sgn}(y)|y|^{q}$ for all real $x,y$.
--
--   Strict monotonicity makes $\mathrm{signedPower}(q,\cdot)$ injective: if two inputs give the same signed power, they must be equal. This underlies its use as an order-preserving change of variables -- for instance in the scalar Mazur map $\psi_p(x)=\mathrm{signedPower}(p/2,x)$ for $p>0$ -- where recovering $x$ from $\psi_p(x)$ reduces to this injectivity, and comparing the order of two scalar quantities after applying the map reduces to the strict monotonicity itself.
--
--   **Formalization Note.** Strict monotonicity alone gives injectivity, not a full two-sided inverse function on $\mathbb R$; producing one additionally needs continuity (`continuous_signedPower`, proved separately for $q>0$) together with the fact that $\mathrm{signedPower}(q,\cdot)$ is unbounded in both directions.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/ScalarBregman.lean#L135-L163

import Definitions.Def_HlawkaSchatten_ScalarBregman
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Instances.Sign

open Filter
open scoped Topology

open HlawkaSchatten

theorem HlawkaSchatten.strictMono_signedPower {q : ℝ} (hq : 0 < q) : StrictMono (signedPower q) := by sorry

-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Auxiliary_exists_auxiliary_packet
-- name    : OAI.AsymptoticallyMinimalLittlewood.Auxiliary.exists_auxiliary_packet
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:11:33.216653+00:00
-- url     : https://prove2.me/theorems/15643e89-72cf-495d-b993-e5e061dd675d
-- title:
--   Existence of a nearly flat Fourier packet with prescribed curvature, width and coefficient-size constraints
-- statement:
--   Notation. Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$. For a finite set $J$, an integer vector $m\in\mathbb{Z}^J$ and $y\in\mathbb{T}^J$ let $e_m(y)=\prod_{j\in J}e^{2\pi i m_j y_j}$, and for $v\in\mathbb{R}^J$ let $\langle m,v\rangle=\sum_{j\in J}m_jv_j$.
--
--   Let $0<\delta<\tfrac1{20}$. Then there exist a nonempty finite index set $Q$, a finite set $J$, integer vectors $m_q\in\mathbb{Z}^J$ and complex numbers $a_q$ for $q\in Q$, and a real vector $v\in\mathbb{R}^J$ such that, with
--   $$
--   F(y)=\sum_{q\in Q}a_q\,e_{m_q}(y)\quad(y\in\mathbb{T}^J),\qquad \lambda_q=\langle m_q,v\rangle,
--   $$
--   the following seven conditions hold.
--
--   1. (Nonzero frequencies) $m_q\ne0$ for every $q\in Q$.
--   2. (No parallel frequencies) For $q\ne q'$ there is no real $t$ with $m_q=t\,m_{q'}$.
--   3. (Flatness) $|F(y)+\overline{F(y)}|\le1$ for every $y\in\mathbb{T}^J$.
--   4. (Energy) $(1-3\delta)^2\le2\sum_{q\in Q}|a_q|^2$.
--   5. (Nonzero curvatures) $\lambda_q\ne0$ for every $q\in Q$.
--   6. (Total width) $2\sum_{q\in Q}|\lambda_q|<1$.
--   7. (Coefficient size) $|a_q|^2\le\dfrac{(1+\delta)^3}{1-\delta}\,|\lambda_q|$ for every $q\in Q$.
--
--   The function $F+\overline F=2\operatorname{Re}F$ is a real trigonometric polynomial on the torus $\mathbb{T}^J$ with supremum norm at most $1$. Conditions 1 and 2 imply that the $2|Q|$ frequencies $\pm m_q$ are pairwise distinct, so by Parseval its mean square equals $2\sum_q|a_q|^2$, which by condition 4 is at least $(1-3\delta)^2$: the polynomial is nearly flat. The velocity $v$ assigns to every frequency a nonzero curvature $\lambda_q$; the total width $2\sum_q|\lambda_q|$ is less than $1$, and each squared coefficient is at most $(1+\delta)^3/(1-\delta)$ times its curvature. For fixed $\delta$, such a packet is the finite input of the subsequent sampling and interval-packing steps, which turn it into real coefficient sequences in $[-1,1]$ with nearly flat exponential sums, on the way to Littlewood polynomials $P$ of length $N$ with $|P(z)|\le(1+\eta)\sqrt N$ on the unit circle.
--
--   **Formalization Note** The data form the structure `FinitePacket δ`: index types `I` (playing the role of $Q$) and `J` with `Fintype` instances, `I` nonempty, and a record `RawData` whose fields `frequency`, `coefficient`, `velocity` are $m$, $a$, $v$ and whose fields `nonzero`, `nonparallel`, `bounded`, `energy`, `curvature`, `width`, `size` are conditions 1 to 7. The theorem asserts `Nonempty (FinitePacket δ)`. The characters $e_m$ are Mathlib's `mFourier`, and parallelism in condition 2 is tested for the vectors viewed in $\mathbb{R}^J$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Spreading.lean#L533-L708

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Auxiliary
universe uI uE uJ uK
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

theorem OAI.AsymptoticallyMinimalLittlewood.Auxiliary.exists_auxiliary_packet {δ : ℝ} (hδ : 0<δ) (hδ20 : δ<1/20) :
    Nonempty (FinitePacket δ) := by sorry

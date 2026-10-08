-- Prove2me | Theorems.Thm_ManyServerFluid_Uniqueness_eq_4_55
-- name    : ManyServerFluid.Uniqueness.eq_4_55
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:40.400991+00:00
-- url     : https://prove2.me/theorems/704b000f-a5ef-489c-846d-6458e135a71e
-- title:
--   (4.55) — ψ_h in closed form: (1−G(x))/(1−G(x−t)) for t ≤ x < M, 1−G(x) for x ≤ t
-- statement:
--   Let $\psi_h(x,t) = \exp(r_h(x,t))$ be the function (4.45)–(4.46) for $\ell = h$, the hazard rate. For $x \in [0,M)$:
--   $$\psi_h(x,t) = \begin{cases}\dfrac{1-G(x)}{1-G(x-t)}, & 0 \le t \le x < M,\\[2mm] 1-G(x), & 0 \le x \le t.\end{cases}$$
--
--   This identity, used at the start of the proof of Theorem 4.1, turns the exponential of the integrated hazard into survival-function ratios, which is where the factors $(1-G(x+t))/(1-G(x))$ and $1-G(t-s)$ of the representation (4.3) come from.
--
--   **Formalization Note.** The paper's (4.55) also lists the value $0$ "otherwise", and writes the second case as $0 \le x \le t < \infty$ without $x < M$. For $x \ge M$ the definition (4.46) gives $r_h = 0$, hence $\psi_h = 1$, not $0$; only values on $[0,M)\times[0,\infty)$ are used. We state the two cases on $[0,M)$, where (4.46) and (4.55) agree.
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), p. 69, proof of Theorem 4.1 (§4.3.4), (4.55); definitions (4.45)–(4.46), p. 67

import Mathlib
import Definitions.Def_ManyServerFluid_Uniqueness_Model
import Definitions.Def_ManyServerFluid_Uniqueness_AgeEquation
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ManyServerFluid.Uniqueness

/-- (4.55), proof of Theorem 4.1, p. 69: ψ_h in closed form on [0, M) × [0, ∞):
ψ_h(x, t) = (1 − G(x))/(1 − G(x − t)) if 0 ≤ t ≤ x < M, and ψ_h(x, t) = 1 − G(x) if 0 ≤ x ≤ t,
x < M. -/
theorem eq_4_55 (S : ServiceLaw) (x t : ℝ) (hx : x ∈ S.Ages) :
    (0 ≤ t → t ≤ x → S.psiEll S.h (x, t) = (1 - S.G x) / (1 - S.G (x - t))) ∧
    (x ≤ t → S.psiEll S.h (x, t) = 1 - S.G x) := by sorry

end ManyServerFluid.Uniqueness

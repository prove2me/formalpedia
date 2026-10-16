-- Prove2me | Theorems.Thm_OAI_QuantumTrace_negMulLog_le_crossEntropy
-- name    : OAI.QuantumTrace.negMulLog_le_crossEntropy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:57:05.842334+00:00
-- url     : https://prove2.me/theorems/63413033-e925-4bec-9cbe-c8ae5265f466
-- title:
--   Pointwise Gibbs inequality $-p\log p\le q-p-p\log q$
-- statement:
--   Let $\eta(x)=-x\log x$ for $x>0$ and $\eta(0)=0$. For all real numbers $p\ge 0$ and $q>0$,
--   $$-p\log p\;\le\; q-p+p\,(-\log q),$$
--   where the left-hand side means $\eta(p)$ (so it is $0$ when $p=0$).
--
--   Equivalently, $p\log(p/q)-p+q\ge 0$: the summand of the generalized relative entropy between nonnegative weights is nonnegative. Summed over an index set, this inequality gives Gibbs' inequality, namely that the entropy of a distribution is at most its cross-entropy against any reference distribution, together with the corresponding summability statements.
--
--   **Formalization Note** $\eta$ is Mathlib's `Real.negMulLog`, which is $0$ at $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/QuantumTrace/Basic.lean#L475-L488

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

theorem OAI.QuantumTrace.negMulLog_le_crossEntropy {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    Real.negMulLog p ≤ q - p + p * (-Real.log q) := by sorry

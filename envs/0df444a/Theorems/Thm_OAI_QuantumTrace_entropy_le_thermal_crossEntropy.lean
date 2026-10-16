-- Prove2me | Theorems.Thm_OAI_QuantumTrace_entropy_le_thermal_crossEntropy
-- name    : OAI.QuantumTrace.entropy_le_thermal_crossEntropy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:58:08.638995+00:00
-- url     : https://prove2.me/theorems/ad2fbd76-ccfe-4c28-b2c9-e10bca4dce6a
-- title:
--   Energy-constrained entropy bound by thermal cross-entropy for a positive trace-one operator
-- statement:
--   Let $E$ be a complex Hilbert space with a Hilbert basis $(b_k)_{k\in\mathbb{N}^n}$ indexed by multi-indices $k=(k_1,\dots,k_n)$, and write $|k|=k_1+\dots+k_n$. Let $T$ be a positive bounded operator on $E$ with diagonal entries $p_k=\operatorname{Re}\langle b_k,Tb_k\rangle$ such that $\sum_kp_k=1$ (a convergent series) and such that the energy series converges, with sum
--   $$N=\sum_{k}|k|\,p_k .$$
--   Let $\eta(x)=-x\log x$ (with $\eta(0)=0$), and let $\eta(T)=-T\log T$ be defined by continuous functional calculus. Then for every $r>0$,
--   $$\sum_{k\in\mathbb{N}^n}\operatorname{Re}\langle b_k,\eta(T)\,b_k\rangle\;\le\;n\log(r+1)+N\log\frac{r+1}{r}.$$
--
--   The left-hand side is the von Neumann entropy $-\operatorname{Tr}T\log T$ computed in the basis $(b_k)$, and the right-hand side is the cross-entropy of the diagonal of $T$ against the $n$-mode thermal distribution of mean $r$ per mode. When $N>0$, the choice $r=N/n$ (for $n\ge 1$) makes the right-hand side equal to $n\,g(N/n)$ with $g(t)=(t+1)\log(t+1)-t\log t$, so the theorem yields the energy-constrained entropy bound $-\operatorname{Tr}T\log T\le n\,g(N/n)$.
--
--   **Formalization Note** $\eta(T)$ is `entropyOperator T`, defined as `cfc Real.negMulLog T`. The left-hand side is written as a `tsum`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/QuantumTrace/Basic.lean#L604-L622

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem OAI.QuantumTrace.entropy_le_thermal_crossEntropy {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive)
    (ht : HasSum (fun k => (inner ℂ (b k) (T (b k))).re) 1)
    (hE : Summable (fun k => (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re))
    {r : ℝ} (hr : 0 < r) :
    (∑' k, (inner ℂ (b k) (entropyOperator T (b k))).re) ≤
      n * Real.log (r + 1) +
      (∑' k, (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re) * Real.log ((r + 1) / r) := by sorry

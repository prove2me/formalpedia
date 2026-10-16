-- Prove2me | Theorems.Thm_OAI_QuantumTrace_tendsto_tsum_of_uniform_tail
-- name    : OAI.QuantumTrace.tendsto_tsum_of_uniform_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:49:52.129285+00:00
-- url     : https://prove2.me/theorems/646a401d-4b7f-437e-9213-e826ebef3175
-- title:
--   Limits of series of nonnegative terms with uniformly small tails
-- statement:
--   Let $\alpha$ and $\iota$ be types, $l$ a filter on $\alpha$, $f:\alpha\times\iota\to\mathbb R$ and $g:\iota\to\mathbb R$. Assume:
--
--   1. for every $a$ the series $\sum_if(a,i)$ converges, and $\sum_ig(i)$ converges;
--   2. $f(a,i)\ge0$ and $g(i)\ge0$ for all $a,i$;
--   3. for every $i$, $f(a,i)\to g(i)$ as $a\to l$;
--   4. (uniform tails) for every $\varepsilon>0$ there is a finite set $s\subseteq\iota$ such that $\sum_{i\notin s}f(a,i)<\varepsilon$ for every $a$ and $\sum_{i\notin s}g(i)<\varepsilon$.
--
--   Then
--
--   $$
--   \lim_{a\to l}\sum_{i\in\iota}f(a,i)=\sum_{i\in\iota}g(i).
--   $$
--
--   This is the elementary "tightness" form of the dominated convergence theorem for series: pointwise convergence plus uniformly small tails gives convergence of the sums. It is used to pass to the limit in traces and energies of sequences of density operators whose energies are uniformly bounded.
--
--   **Formalization Note** The limit is `Filter.Tendsto` along an arbitrary filter $l$ (no nontriviality is needed), and the tail sums are `tsum`s over the subtype of indices outside $s$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Entropy.lean#L381-L412

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy

open OAI OAI.QuantumTrace
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open Filter Topology

theorem OAI.QuantumTrace.tendsto_tsum_of_uniform_tail {α ι : Type*} {l : Filter α}
    {f : α → ι → ℝ} {g : ι → ℝ}
    (hf : ∀ a, Summable (f a)) (hg : Summable g)
    (hfp : ∀ a i, 0 ≤ f a i) (hgp : ∀ i, 0 ≤ g i)
    (hlim : ∀ i, Tendsto (fun a => f a i) l (𝓝 (g i)))
    (htail : ∀ ε > 0, ∃ s : Finset ι,
      (∀ a, (∑' i : {i // i ∉ s}, f a i) < ε) ∧
      (∑' i : {i // i ∉ s}, g i) < ε) :
    Tendsto (fun a => ∑' i, f a i) l (𝓝 (∑' i, g i)) := by sorry

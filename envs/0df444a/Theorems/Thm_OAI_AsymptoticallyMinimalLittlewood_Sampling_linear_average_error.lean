-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_linear_average_error
-- name    : OAI.AsymptoticallyMinimalLittlewood.Sampling.linear_average_error
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:54:57.380241+00:00
-- url     : https://prove2.me/theorems/a5f2d270-743f-4d64-971c-61a79177412c
-- title:
--   Poisson summation for linearly modulated Riemann sums with an $O(N^{-2})$ error
-- statement:
--   Let $g:\mathbb{R}\to\mathbb{C}$ be smooth with compact support, with closed support contained in $[-A,A]$ for some $A\ge0$. Let $b\in\mathbb{R}$ and let $S\subset\mathbb{Z}$ be a finite set such that every integer $l\notin S$ satisfies $l\neq b$ (automatic if $b\notin\mathbb{Z}$; if $b\in\mathbb{Z}$ it means $b\in S$).
--
--   Then there is a constant $C\ge0$ such that for every real $N>0$,
--   $$
--   \Bigl|\frac1N\sum_{k\in\mathbb{Z}}g\Bigl(\frac kN\Bigr)e^{2\pi ibk}-\sum_{l\in S}\int_{\mathbb{R}}g(x)\,e^{-2\pi iN(l-b)x}\,dx\Bigr|\le\frac{C}{N^2}.
--   $$
--   (The sum over $k$ has finitely many nonzero terms since $g$ has compact support.)
--
--   So the resonant integers $l\in S$ contribute the integrals $\int g(x)e^{-2\pi iN(l-b)x}\,dx$ (for $l=b$ this is $\int g$), while all other dual frequencies together contribute only $O(N^{-2})$. Two special cases enter the mean-square analysis of sampled chirp sums: with $b=0$ and $S=\{0\}$ the Riemann sum $\frac1N\sum_k g(k/N)$ equals $\int g$ up to $O(N^{-2})$; with $b\notin\mathbb{Z}$ and $S=\varnothing$ the twisted average $\frac1N\sum_k g(k/N)e^{2\pi ibk}$ is $O(N^{-2})$, which handles cross terms between modes of equal curvature.
--
--   **Formalization Note** The exponentials are written `phase 0 (-b) k` $=e^{2\pi ibk}$ and `phase 0 (N*(l-b)) x` $=e^{-2\pi iN(l-b)x}$, where `phase t u x` $=\exp(2\pi i(tx^2/2-ux))$; the sum over $k$ is a `tsum` over $\mathbb{Z}$. The constant $C$ may depend on $g$, $A$, $b$ and $S$, but not on $N$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SamplingEnergy.lean#L69-L134

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail
import Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

theorem OAI.AsymptoticallyMinimalLittlewood.Sampling.linear_average_error {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {A : ℝ} (hA : 0≤A)
    (hsupp : tsupport g⊆Set.Icc (-A) A) (b : ℝ) (S : Finset ℤ)
    (hres : ∀ l∉S, (l : ℝ)≠b) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℝ, 0<N →
      ‖(1/(N : ℂ))*(∑' k : ℤ, g ((k : ℝ)/N)*phase 0 (-b) k)-
        ∑ l∈S, ∫ x : ℝ, g x*phase 0 (N*((l : ℝ)-b)) x‖≤C/N^2 := by sorry

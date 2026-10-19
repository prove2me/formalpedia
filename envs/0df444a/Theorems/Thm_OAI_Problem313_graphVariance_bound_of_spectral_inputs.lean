-- Prove2me | Theorems.Thm_OAI_Problem313_graphVariance_bound_of_spectral_inputs
-- name    : OAI.Problem313.graphVariance_bound_of_spectral_inputs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:51:10.089399+00:00
-- url     : https://prove2.me/theorems/acd93a77-af27-40b9-850d-f10f6141846b
-- title:
--   Variance at most $2^{17}(\log n)^{-2}$ times total influence
-- statement:
--   For a graph property $f$ on $n$ labelled vertices and $0<p<1$, let $\hat f(S)$ be the $p$-biased Fourier coefficients of $[f]$ over edge sets $S$, $I_e^p(f)$ the probability that edge $e$ is pivotal, and $I^p(f)=\sum_eI_e^p(f)$. An edge touches a vertex block $B$ if it has an endpoint in $B$. Let $n\ge2$ and suppose:
--
--   1. $\mathrm{Var}_p(f)=\sum_{S\ne\emptyset}\hat f(S)^2$;
--   2. $\sum_S|S|\hat f(S)^2=p(1-p)I^p(f)$;
--   3. if $\log n\ge16$, then with $m=\lfloor\sqrt n\rfloor$ and $\sigma=\sqrt{p(1-p)}$, the mass on $1\le|S|\le(\sigma\log m/64)^2/2$ is at most $4m^{-1/4}I^p(f)$.
--
--   Then
--   $$
--   \mathrm{Var}_p(f)\le\frac{2^{17}}{(\log n)^2}\,I^p(f) .
--   $$
--
--   This is the graph form of the Bourgain–Kalai-type variance–influence inequality. After these spectral inputs, no symmetry is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/GraphVarianceBound.lean#L14-L50

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype
import Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierProjection
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOptionExpectation

open OAI OAI.Problem313

theorem OAI.Problem313.graphVariance_bound_of_spectral_inputs {n : ℕ}
    (f : GraphConfig n → Bool) (p : ℝ) (hn : 2 ≤ n) (hp : 0 < p) (hp1 : p < 1)
    (hvariance : graphVariance p f =
      ∑ S : Finset (GraphEdge n) with S.Nonempty,
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2)
    (hdirichlet : (∑ S : Finset (GraphEdge n), (S.card : ℝ) *
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) =
      p * (1 - p) * totalInfluence p f)
    (hcapture : 16 ≤ Real.log (n : ℝ) →
      (∑ S : Finset (GraphEdge n) with S.Nonempty ∧
          (S.card : ℝ) ≤ (Real.sqrt (p * (1 - p)) *
            Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2,
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) ≤
      (4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ)) * totalInfluence p f) :
    graphVariance p f ≤
      ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) * totalInfluence p f := by sorry

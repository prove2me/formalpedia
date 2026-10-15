-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_center_sum_comparison_of_bounds
-- name    : OAI.FixedClauseThreshold.center_sum_comparison_of_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T05:12:54.589982+00:00
-- url     : https://prove2.me/theorems/1e1eb257-5214-4d5a-8fc9-e8d74fb58d3b
-- title:
--   Approximate min-superadditivity of random $k$-SAT centers under explicit error bounds
-- statement:
--   Fix a clause size $k\ge 3$. Let $\gamma_k(n)$ denote the *normalized center* of the random proper $k$-SAT model on $n$ variables: draw $M=2^{k+1}n$ independent uniformly random proper $k$-clauses $C_1,\dots,C_M$ (each clause uses $k$ distinct variables chosen uniformly among $x_1,\dots,x_n$, with independent fair signs), let the *satisfiable lifetime* $L_n$ be the number of indices $j\in\{1,\dots,M\}$ for which $C_1\wedge\cdots\wedge C_j$ is satisfiable, and set $\gamma_k(n)=\mathbb{E}[L_n]/n$. Put
--
--   $$
--   \delta_k=\frac{k-2}{4k},\qquad w_k(n)=n^{1-\delta_k},\qquad \varepsilon_k(n)=V_k\,n^{-2\delta_k},\qquad V_k=2\,(2^{k+1})^3\,k\,(2k+2^{k+1}+2).
--   $$
--
--   $$
--   \rho_k(n)=\frac{2^{k+1}\,n}{w_k(n)^2},\qquad \kappa_k=\frac12\exp\Bigl(-2\cdot 2^{k+1}\tbinom{k}{2}\Bigr).
--   $$
--
--   (fluctuation window, concentration error, sampling error and transfer constant).
--
--   **Theorem.** Let $r,s$ be natural numbers, write $u=\min(r,s)$, and assume
--
--   1. $r\ge k+1$, $s\ge k+1$, $r\ge 2\binom{k}{2}$ and $s\ge 2\binom{k}{2}$;
--   2. $\varepsilon_k(r)\le\frac12$ and $\varepsilon_k(s)\le\frac12$;
--   3. $\rho_k(r)\le\frac14$ and $\rho_k(s)\le\frac14$;
--   4. $\varepsilon_k(r+s)<\kappa_k^2/2$;
--   5. $2\,u^{-\delta_k}\le\min\bigl(\gamma_k(r),\gamma_k(s)\bigr)$.
--
--   Then
--
--   $$
--   \min\bigl(\gamma_k(r),\gamma_k(s)\bigr)-4\,u^{-\delta_k}\le\gamma_k(r+s).
--   $$
--
--   The normalized center of a system on $r+s$ variables is thus at least the smaller of the two block centers, up to an error that decays polynomially in the smaller block size. Together with a similar comparison between $s$ and $s+1$ variables, this approximate min-superadditivity is what forces the centers $\gamma_k(n)$ to converge.
--
--   **Formalization Note** In Lean the error term is `densityWindow (min r s) k`, i.e. $u^{-\delta_k}$; `repeatPairs k` is $\binom{k}{2}$ as a real number, and the other quantities are `concentrationError`, `samplingError`, `transferLower` and `center`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/CenterComparison.lean#L169-L229

import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds
import Definitions.Def_OAI_Probability_RandomSAT_Interpolation
import Definitions.Def_OAI_Probability_RandomSAT_Transfer
import Definitions.Def_OAI_Probability_RandomSAT_CenterComparison

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.center_sum_comparison_of_bounds {r s k : ℕ} (hk : 3 ≤ k)
    (hr : k + 1 ≤ r) (hs : k + 1 ≤ s)
    (hrrep : 2 * repeatPairs k ≤ r) (hsrep : 2 * repeatPairs k ≤ s)
    (hrerr : concentrationError r k ≤ 1 / 2) (hserr : concentrationError s k ≤ 1 / 2)
    (hrsample : samplingError r k ≤ 1 / 4) (hssample : samplingError s k ≤ 1 / 4)
    (hNerr : concentrationError (r + s) k < (transferLower k)^2 / 2)
    (hlow : 2 * densityWindow (min r s) k ≤ min (center r k) (center s k)) :
    min (center r k) (center s k) - 4 * densityWindow (min r s) k ≤ center (r + s) k := by sorry

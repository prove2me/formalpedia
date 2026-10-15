-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_auxiliary_interpolation_center_lower
-- name    : OAI.FixedClauseThreshold.auxiliary_interpolation_center_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T05:11:11.289387+00:00
-- url     : https://prove2.me/theorems/93d6b354-c09c-4ad4-bc62-a5c44aa83e49
-- title:
--   Two-block interpolation lower bound for the auxiliary $k$-SAT satisfiability probability
-- statement:
--   Fix a clause size $k\ge 3$; for a number of variables $n\ge 1$ write the Boolean variables as $x_1,\dots,x_n$.
--
--   For $m\ge 0$ let $Q_k(n,m)$ be the *auxiliary satisfiability probability*: the probability that $m$ independent random auxiliary $k$-clauses on $x_1,\dots,x_n$ have a common satisfying assignment. An auxiliary $k$-clause is an ordered list of $k$ literals drawn independently, each with a uniformly random variable among $x_1,\dots,x_n$ and an independent fair sign (variables may repeat); it is satisfied when at least one of its literals is true.
--
--   Let $\gamma_k(n)$ denote the *normalized center* of the random proper $k$-SAT model on $n$ variables: draw $M=2^{k+1}n$ independent uniformly random proper $k$-clauses $C_1,\dots,C_M$ (each clause uses $k$ distinct variables chosen uniformly among $x_1,\dots,x_n$, with independent fair signs), let the *satisfiable lifetime* $L_n$ be the number of indices $j\in\{1,\dots,M\}$ for which $C_1\wedge\cdots\wedge C_j$ is satisfiable, and set $\gamma_k(n)=\mathbb{E}[L_n]/n$.
--
--   Finally put
--
--   $$
--   \delta_k=\frac{k-2}{4k},\qquad w_k(n)=n^{1-\delta_k},\qquad \varepsilon_k(n)=V_k\,n^{-2\delta_k},\qquad V_k=2\,(2^{k+1})^3\,k\,(2k+2^{k+1}+2).
--   $$
--
--   $$
--   \rho_k(n)=\frac{2^{k+1}\,n}{w_k(n)^2},\qquad \kappa_k=\frac12\exp\Bigl(-2\cdot 2^{k+1}\tbinom{k}{2}\Bigr).
--   $$
--
--   Here $w_k$ is the fluctuation window, $\varepsilon_k$ the concentration error, $\rho_k$ the sampling error and $\kappa_k$ the transfer constant.
--
--   **Theorem.** Let $k\ge 3$ and let $r,s,m$ be natural numbers such that
--
--   1. $r\ge k+1$, $s\ge k+1$, $r\ge 2\binom{k}{2}$ and $s\ge 2\binom{k}{2}$;
--   2. $\varepsilon_k(r)\le\frac12$ and $\varepsilon_k(s)\le\frac12$;
--   3. $m\le 2^{k+1}(r+s)$;
--   4. $m\,\dfrac{r}{r+s}+2\,w_k(r)\le r\,\gamma_k(r)$ and $m\,\dfrac{s}{r+s}+2\,w_k(s)\le s\,\gamma_k(s)$.
--
--   Then
--
--   $$
--   \kappa_k^2\,\bigl(1-\rho_k(r)-\rho_k(s)\bigr)\le Q_k(r+s,\,m).
--   $$
--
--   Condition 4 says that the proportional share of the $m$ clauses belonging to each block of variables (sizes $r$ and $s$) lies at least two fluctuation windows below that block's mean lifetime. The theorem concludes that the auxiliary system of $m$ clauses on all $r+s$ variables is then satisfiable with probability at least a constant depending only on $k$, up to the sampling errors $\rho_k(r)$ and $\rho_k(s)$. It is the key estimate behind the approximate superadditivity of the centers $\gamma_k$.
--
--   **Formalization Note** The objects are `auxiliaryProbability (r + s) k m`, `center`, `fluctuationWindow`, `concentrationError`, `samplingError` and `transferLower`; `repeatPairs k` is $\binom{k}{2}$ as a real number and `capMultiplier k` is $2^{k+1}$. All inequalities are between real numbers, with $r,s,m$ cast to $\mathbb{R}$; since $r,s>0$ the quotients $r/(r+s)$ and $s/(r+s)$ are ordinary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/CenterComparison.lean#L18-L91

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

theorem OAI.FixedClauseThreshold.auxiliary_interpolation_center_lower {r s k m : ℕ} (hk : 3 ≤ k)
    (hr : k + 1 ≤ r) (hs : k + 1 ≤ s)
    (hrrep : 2 * repeatPairs k ≤ r) (hsrep : 2 * repeatPairs k ≤ s)
    (hrerr : concentrationError r k ≤ 1 / 2) (hserr : concentrationError s k ≤ 1 / 2)
    (hm : (m : ℝ) ≤ (capMultiplier k : ℝ) * ((r : ℝ) + s))
    (hgapr : (m : ℝ) * ((r : ℝ) / (r + s)) + 2 * fluctuationWindow r k ≤ (r : ℝ) * center r k)
    (hgaps : (m : ℝ) * ((s : ℝ) / (r + s)) + 2 * fluctuationWindow s k ≤ (s : ℝ) * center s k) :
    (transferLower k)^2 * (1 - samplingError r k - samplingError s k) ≤
      auxiliaryProbability (r + s) k m := by sorry

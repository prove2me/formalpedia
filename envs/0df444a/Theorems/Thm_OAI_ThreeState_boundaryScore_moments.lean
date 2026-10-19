-- Prove2me | Theorems.Thm_OAI_ThreeState_boundaryScore_moments
-- name    : OAI.ThreeState.boundaryScore_moments
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:45:57.463104+00:00
-- url     : https://prove2.me/theorems/ca4ae3b3-1eb8-415b-a4b8-ef6b373dba68
-- title:
--   Mean and second moment of the boundary score of a Galton–Watson broadcast tree
-- statement:
--   Throughout, a spin is an element of $\{0,1,2\}$. A parameter $\lambda\in\mathbb{R}$ is admissible if $-\tfrac12\le\lambda\le1$; then the symmetric channel $M_\lambda(i,j)=\tfrac{1+2\lambda}{3}$ for $j=i$ and $M_\lambda(i,j)=\tfrac{1-\lambda}{3}$ for $j\ne i$ is a stochastic matrix.
--
--   **Observations.** A depth-$0$ observation is a spin, and a depth-$(n+1)$ observation is a finite multiset of depth-$n$ observations. Fix an offspring distribution $\mu$ on $\mathbb{N}$. $\mathcal L_0(i)$ is the point mass at $i$. To sample from $\mathcal L_{n+1}(i)$, draw $K\sim\mu$, then $K$ independent pairs (child spin $j\sim M_\lambda(i,\cdot)$, observation from $\mathcal L_n(j)$), and record the multiset of the $K$ observations.
--
--   **Scores.** The spin score is $\sigma(0)=2$, $\sigma(1)=\sigma(2)=-1$. The boundary score $S_n$ of a depth-$n$ observation is defined by $S_0(y)=\sigma(y)$ and $S_{n+1}(\{y_1,\dots,y_k\})=\sum_jS_n(y_j)$, i.e. the sum of the spin scores of generation $n$. For $d,e\in\mathbb{R}$ let
--   $$
--   Q_0(i)=\sigma(i)^2,\qquad Q_{n+1}(i)=d\sum_{j}M_\lambda(i,j)\,Q_n(j)+e\bigl((d\lambda)^n\lambda\,\sigma(i)\bigr)^2 .
--   $$
--
--   **Statement.** Let $\lambda$ be admissible, and let $d,e\in\mathbb{R}$. Assume the offspring count $K\sim\mu$ has finite second moment, with $\mathbb{E}[K]=d$ and $\mathbb{E}[K^2]=e+d$ (so $e=\mathbb{E}[K(K-1)]$). Then for every $n\in\mathbb{N}$ and every root spin $i$, $S_n$ has finite second moment under $\mathcal L_n(i)$, and
--   $$
--   \mathbb{E}_{\mathcal L_n(i)}[S_n]=(d\lambda)^n\,\sigma(i),\qquad \mathbb{E}_{\mathcal L_n(i)}\bigl[S_n^2\bigr]=Q_n(i).
--   $$
--
--   The mean grows like $(d\lambda)^n$, while the recursion for $Q_n$ shows that the second moment grows like $\max\bigl(d,(d\lambda)^2\bigr)^n$. Above the Kesten–Stigum threshold $d\lambda^2>1$ the signal therefore dominates the noise, which is the basis of the reconstruction proofs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeState/Supercritical.lean#L82-L102

import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations
import Definitions.Def_OAI_Probability_ThreeState_Messages
import Definitions.Def_OAI_Probability_ThreeState_Observation
import Definitions.Def_OAI_Probability_ThreeState_Update
import Definitions.Def_OAI_Probability_ThreeState_RadialMoments
import Definitions.Def_OAI_Probability_ThreeState_RadialDerivatives
import Definitions.Def_OAI_Probability_ThreeState_PosteriorMoments
import Definitions.Def_OAI_Probability_ThreeState_PoissonCritical
import Definitions.Def_OAI_Probability_ThreeState_Supercritical

open OAI OAI.ThreeState

theorem OAI.ThreeState.boundaryScore_moments (offspring : PMF ℕ) (d e lam : ℝ) (h : Admissible lam)
    (hD : Moments offspring (fun k : ℕ => (k:ℝ)) d (e+d)) (n : ℕ) (i : Spin) :
    Moments (observedLaw offspring lam h n i) (boundaryScore n)
      ((d*lam)^n*spinScore i) (scoreSecond d e lam h n i) := by sorry

-- Prove2me | Theorems.Thm_OAI_BufferedIsing_extremeLogOdds_eq_actualCoupling
-- name    : OAI.BufferedIsing.extremeLogOdds_eq_actualCoupling
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:22:13.090397+00:00
-- url     : https://prove2.me/theorems/bd259329-e848-4362-9264-64e61caa5e99
-- title:
--   Extreme log-odds of the pinned two-block marginal equal four times an effective coupling on the contracted graph
-- statement:
--   Let $G$ be a finite graph on the vertex set $V=\{0,\dots,n-1\}$ with separately indexed edges $e$ (parallel edges allowed), endpoints $\ell(e)\neq r(e)$ and couplings $K_e\ge0$, let $h\in\mathbb{R}^V$ be an arbitrary field, and $w_h(\sigma)=\exp\big(\sum_eK_e\sigma_{\ell(e)}\sigma_{r(e)}+\sum_vh_v\sigma_v\big)$. Let $I,J,F\subseteq V$ be pairwise disjoint, fix $\tau\in\{-1,+1\}^V$ and vertices $i\in I$, $j\in J$. For $a,b\in\{-1,+1\}^V$ let $Z_\tau(a,b)$ be the total weight of the configurations that equal $a$ on $I$, $b$ on $J$ and $\tau$ on $F$, and define the *extreme log-odds*
--   $$
--   \Lambda_\tau=\log Z_\tau(\underline{+},\underline{+})+\log Z_\tau(\underline{-},\underline{-})-\log Z_\tau(\underline{+},\underline{-})-\log Z_\tau(\underline{-},\underline{+}),
--   $$
--   where $\underline{\pm}$ is the constant configuration with all spins equal to $\pm1$.
--
--   The *actual comparison graph* $\widehat G$ is obtained from $G$ by deleting $F$ together with all edges meeting it, identifying all vertices of $I$ into one vertex $\hat\imath$ and all vertices of $J$ into one vertex $\hat\jmath$, discarding the self-loops this creates (edges inside $I$ or inside $J$), keeping every other edge (parallel edges included) with its coupling, and relabelling the vertices by integers. Its field $\hat h$ is, at each vertex of $\widehat G$, the sum over the merged original vertices of the fields induced by the pins,
--   $$
--   h^{F,\tau}_v=h_v+\sum_{e:\ \ell(e)=v,\ r(e)\in F}K_e\tau_{r(e)}+\sum_{e:\ r(e)=v,\ \ell(e)\in F}K_e\tau_{\ell(e)}\qquad(v\notin F),
--   $$
--   so that for instance $\hat h_{\hat\imath}=\sum_{v\in I}h^{F,\tau}_v$. With $T^{x,y}[W](s,t)=\sum_\sigma\mathbf 1[\sigma_x=s,\ \sigma_y=t]\,W(\sigma)$ the two-site table at $(x,y)$ of a weight $W$ and $\mathcal K(w)=\tfrac14\big(\log w(+,+)+\log w(-,-)-\log w(+,-)-\log w(-,+)\big)$ the effective coupling of a $2\times2$ table:
--
--   **Theorem.**
--   $$
--   \Lambda_\tau=4\,\mathcal K\Big(T^{\hat\imath,\hat\jmath}\big[w^{\widehat G}_{\hat h}\big]\Big).
--   $$
--
--   The extreme log-odds controls every ratio of conditional probabilities of the spins on $I$ under different prescriptions on $J$. The theorem identifies it exactly with four times the effective coupling between the two terminals of a genuine ferromagnetic Ising model, in which the common pins survive only through the finite, possibly signed, fields $\hat h$. This is what allows a comparison with the zero-field model on the same graph $\widehat G$, whose effective coupling is the inverse hyperbolic tangent of the random-cluster connection probability between the terminals.
--
--   **Formalization Note** $\Lambda_\tau$ is `extremeLogOdds G h I J F τ`, where `⊤` and `⊥` are the all-`true` and all-`false` configurations. $\widehat G$ is `actualComparisonGraph G I J F`, i.e. `interactionGraph (contractedInteraction G I J F)`; $\hat h$ is `actualComparisonField G h I J F τ`; and $\hat\imath,\hat\jmath$ are `actualTerminal G I J F i` and `actualTerminal G I J F j`, with integer labels from `Fintype.equivFin`. The vertices are `i j : KeptVertex F` with `i.val ∈ I`, `j.val ∈ J`. Under the disjointness hypotheses every logarithm is of a positive number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Contraction.lean#L315-L340

import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction

open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem OAI.BufferedIsing.extremeLogOdds_eq_actualCoupling {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) (τ : Spins n) :
    extremeLogOdds G h I J F τ = 4 * tableCoupling (pairTable
      (weight (actualComparisonGraph G I J F) (actualComparisonField G h I J F τ))
      (actualTerminal G I J F i) (actualTerminal G I J F j)) := by sorry

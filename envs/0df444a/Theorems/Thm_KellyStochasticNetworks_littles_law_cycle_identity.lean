-- Prove2me | Theorems.Thm_KellyStochasticNetworks_littles_law_cycle_identity
-- name    : KellyStochasticNetworks.littles_law_cycle_identity
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:27:41.329403+00:00
-- url     : https://prove2.me/theorems/44afaf9c-88a8-4993-bd17-33ee12c35c52
-- title:
--   Equation (2.6) — the cycle identity behind Little's law
-- statement:
--   Little's law, $L = \lambda W$, relates the mean number of customers in a system, the mean
--   arrival rate and the mean time a customer spends in the system. Given the three defining
--   limits, the book's proof reduces it to a single pathwise identity over one regeneration cycle
--   $[0, T_1]$, equation (2.6):
--   $$\int_0^{T_1} n(s)\,ds = \sum_{i=1}^{N} W_i ,$$
--   where $n(s)$ is the number of customers present at time $s$, $N$ is the number of customers
--   arriving in the cycle, and $W_i$ is the time customer $i$ spends in the system. That identity
--   is what is asserted here.
--
--   Let $N$ customers have arrival times $a_i$ and departure times $d_i$ satisfying
--   $0 \le a_i \le d_i \le T$, and let
--   $$n(s) = \#\{i : a_i \le s < d_i\}$$
--   be the number present at time $s$. Then
--   $$\int_0^{T} n(s)\,ds = \sum_{i=1}^{N}(d_i - a_i).$$
--
--   Both sides compute the shaded area of Figure 2.7: the left as an integral over time, the right
--   as a sum over customers. Equivalently, if each customer pays at rate $1$ per unit time while in
--   the system, the two sides are the total paid during the cycle, computed in two ways.
--
--   **Formalization Note** The count $n(s)$ is written as a finite sum of indicator functions of
--   the half-open intervals $[a_i, d_i)$, which is exactly the number of customers present. The
--   hypothesis $d_i \le T$ says every customer who arrives in the cycle also departs within it,
--   which is the assumption $n(T_1) = 0$ of the book's regeneration point; the hypothesis
--   $a_i \le d_i$ excludes a customer departing before arriving. Nothing probabilistic is
--   involved: this is the pathwise half of Little's law, and the three limit statements the book
--   quotes from renewal theory are not part of it.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 37 (PDF p. 45), Theorem 2.13 (Little's law) and equation (2.6) in its proof: 'Thus, it suffices to show int_0^{T_1} n(s) ds = sum_{i=1}^{N} W_i. (2.6) Figure 2.7 illustrates this equality for a simple queue: the shaded area can be calculated as an integral over time, or as a sum over customers.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration

namespace KellyStochasticNetworks

theorem littles_law_cycle_identity {N : ℕ} (T : ℝ) (a d : Fin N → ℝ)
    (ha : ∀ i, 0 ≤ a i) (had : ∀ i, a i ≤ d i) (hd : ∀ i, d i ≤ T) :
    (∫ s in (0:ℝ)..T, occupancy a d s) = ∑ i, (d i - a i) := by sorry

end KellyStochasticNetworks

-- Prove2me | Theorems.Thm_KellyStochasticNetworks_erlang_formula
-- name    : KellyStochasticNetworks.erlang_formula
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T05:51:35.69811+00:00
-- url     : https://prove2.me/theorems/0a5dbcf3-a7d6-413c-a31a-05b42864c43e
-- title:
--   Erlang's formula: the blocking probability of a link with $C$ circuits
-- statement:
--   A telephone link has $C$ parallel circuits. Calls arrive as a Poisson process of rate
--   $\lambda > 0$; each call holds one circuit for an exponentially distributed time of parameter
--   $\mu > 0$, independently of the other calls and of the arrival process; a call that finds every
--   circuit busy is lost. Let $X(t)$ be the number of busy circuits, a Markov process on
--   $\{0,1,\dots,C\}$ with transition rates
--   $$q(j,j+1) = \lambda \quad (j = 0,\dots,C-1), \qquad q(j,j-1) = j\mu \quad (j = 1,\dots,C).$$
--
--   Let $\pi = (\pi(j))_{j=0}^{C}$ satisfy the detailed balance equations for these rates and be
--   normalized, $\sum_{j=0}^{C} \pi(j) = 1$. Then the equilibrium probability that all $C$
--   circuits are busy is
--   $$\pi(C) = E\!\left(\frac{\lambda}{\mu}, C\right), \qquad
--     E(\nu, C) = \frac{\nu^{C}/C!}{\sum_{j=0}^{C} \nu^{j}/j!}.$$
--
--   This is **Erlang's formula**, equation (1.5) of Kelly and Yudovina, *Stochastic Networks*. It
--   is the blocking probability of the link: by the PASTA property, Poisson arrivals see time
--   averages, so $E(\lambda/\mu, C)$ is also the probability that an arriving call is lost. It is
--   the quantity a network operator dimensions against, and the building block from which the
--   loss networks of Chapter 3 are assembled.
--
--   **Formalization Note** The blocking state is the last element of the index type `Fin (C + 1)`.
--   The hypothesis is detailed balance rather than the equilibrium equations, matching the book's
--   derivation; detailed balance is the stronger of the two.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 19 (PDF p. 27), equation (1.5): 'The equilibrium probability that all circuits are busy is therefore pi(C) = E(lambda/mu, C) where E(nu,C) = (nu^C/C!) / sum_{j=0}^{C} nu^j/j!. This is known as Erlang's formula.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Erlang

namespace KellyStochasticNetworks

theorem erlang_formula (lam mu : ℝ) (C : ℕ) (hlam : 0 < lam) (hmu : 0 < mu)
    (π : Fin (C + 1) → ℝ) (h : DetailedBalance π (erlangRates lam mu C))
    (hsum : ∑ j, π j = 1) :
    π (Fin.last C) = erlang (lam / mu) C := by sorry

end KellyStochasticNetworks

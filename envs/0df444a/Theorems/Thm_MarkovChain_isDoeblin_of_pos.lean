-- Prove2me | Theorems.Thm_MarkovChain_isDoeblin_of_pos
-- name    : MarkovChain.isDoeblin_of_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T19:20:30.777827+00:00
-- url     : https://prove2.me/theorems/91c6b3c1-0766-4811-9709-6c7a34f5243b
-- title:
--   A matrix with positive entries satisfies Doeblin's condition
-- statement:
--   Doeblin's condition is not an exotic hypothesis: any transition matrix all of whose entries are at least some $c > 0$ satisfies it, with the uniform distribution as the minorizing measure and constant $\varepsilon = |S|\,c$, where $|S|$ is the number of states. Indeed $\varepsilon \cdot \mathrm{unif}_j = |S|\,c \cdot |S|^{-1} = c \le M_{ij}$. (The constant is automatically at most $1$, since a row of $|S|$ entries each at least $c$ sums to $1$.) This is what connects the abstract minorization hypothesis to the concrete criterion — positivity of the transition matrix, or of one of its powers — under which textbooks state the convergence theorem.
-- source:
--   W. Doeblin, Expose de la theorie des chaines simples constantes de Markov a un nombre fini d'etats, Revue Mathematique de l'Union Interbalkanique 2 (1938), 77-105; the minorization condition and the resulting geometric convergence. Modern account: D. A. Levin, Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Chapter 1 (stationary distributions, reversibility) and Chapter 4 (total variation distance, convergence to equilibrium)

import Definitions.Def_MarkovChain

open Finset Matrix Filter Topology

namespace MarkovChain

theorem isDoeblin_of_pos {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} {c : ℝ} (hne : Nonempty n)
    (hc : 0 < c) (h : ∀ i j, c ≤ M i j) :
    IsDoeblin M (Fintype.card n * c) (unif n) := by
  sorry

end MarkovChain

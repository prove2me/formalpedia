-- Prove2me | Theorems.Thm_LiuPass_condEPPRG_of_owf
-- name    : LiuPass.condEPPRG_of_owf
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-20T22:40:29.972794+00:00
-- url     : https://prove2.me/theorems/6f075af9-1bc2-4236-a8c0-e9d61513a575
-- title:
--   Theorem 5.5: conditionally secure entropy-preserving PRGs from one-way functions
-- statement:
--   Theorem 5.5 of the paper. Assume one-way functions exist. Then there is a polynomial $t_0$ such
--   that for all $\gamma > 1$ and $\delta > 1$ there exists a $\frac{1}{n^{\delta}}$-condEP-PRG
--   $$G : \{0,1\}^n \to \{0,1\}^{n + \gamma \log n}$$
--   whose running time on inputs of length $n$ is bounded by $(\gamma + \delta)\, t_0(n)$.
--
--   That is, conditioned on a sequence of events $E_n$, the output of $G$ on a uniform seed is
--   $n^{-\delta}$-indistinguishable from uniform and still carries Shannon entropy $n - O(\log n)$.
--   The construction starts from Lemma 5.2 (any one-way function is regular on a $1/n$-dense
--   subdomain), applies the hash-based pseudorandom generator for regular one-way functions of
--   Lemma 5.1, and takes the conditioning event to be "the guessed regularity is correct and the seed
--   lies in the dense set". Crucially the entropy notion is Shannon entropy: the known PRG
--   constructions from arbitrary one-way functions are not entropy preserving, and the conditional
--   variant is what makes an arbitrary one-way function suffice.
-- source:
--   Yanyi Liu, Rafael Pass, On One-way Functions and Kolmogorov Complexity, arXiv:2009.11514v1 (FOCS 2020), https://arxiv.org/abs/2009.11514, p. 15, Theorem 5.5

import Definitions.Def_LiuPass_crypto
open Finset
open scoped Classical

namespace LiuPass

open Finset
open scoped Classical

theorem condEPPRG_of_owf (U : UMachine) (hf : ∃ f : BitStr → BitStr, IsOWF U f) :
    ∃ t₀ : ℕ → ℕ, IsPoly t₀ ∧ ∀ gamma delta : ℕ, 1 < gamma → 1 < delta →
      ∃ G : BitStr → BitStr,
        IsCondEPPRG U gamma (fun n => 1 / (n : ℝ) ^ delta) G ∧
        ComputesInTime U (fun n => (gamma + delta) * t₀ n) G := by sorry
end LiuPass

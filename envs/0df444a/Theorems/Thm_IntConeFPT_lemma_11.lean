-- Prove2me | Theorems.Thm_IntConeFPT_lemma_11
-- name    : IntConeFPT.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:57.725259+00:00
-- url     : https://prove2.me/theorems/62712295-03ee-4142-8ac8-19b8d44f9673
-- title:
--   Lemma 11 (Bounding Box) — every point of $K_R(\gamma)$ lies in $[-T,T]$ with $T=\max\{1,N_{\max}M\}$
-- statement:
--   Let $I$ be a valid instance and $M\ge1$ an integer with $P^{(t)}\subseteq[-M,M]^{d+k}$ for every type (for example the $M$ of (2.1)). For every $N_{\max}\in\mathbb Z_{\ge0}$, every candidate tuple $R$ ($|R^{(t)}|\le2^d$), every $\gamma\in\mathbb Q$ and every point of $K_R(\gamma)$, each block satisfies
--   $$
--   \max\big(\|(z^{(t)}_r,w^{(t)}_r)\|_\infty,\ n^{(t)}_r\big)\le T:=\max\{1,N_{\max}M\},
--   $$
--   and the binary length of $T$ is at most the binary length of $N_{\max}$ plus that of $M$.
--
--   With (2.1) this gives the printed $\mathrm{enc}(T)=|I|^{O(1)}$, which is the bounding box needed by Dadush's algorithm in Lemma 13.
--
--   **Formalization Note** `Nat.size` is the binary length of a natural number.
--
--   Differences from the source:
--   - generalization: M is the box bound of (2.1) → every integer M ≥ 1 with P^(t) ⊆ [−M, M]^{d+k} for all t; reason: the M of (2.1) is one such M
--   - generalization: enc(T) = |I|^{O(1)} → Nat.size T ≤ Nat.size N_max + Nat.size M; reason: with enc(M) = |I|^{O(1)} from (2.1) and enc(N_max) ≤ |I| (p.11) the explicit bound gives the printed one
--   - encoding: types t ∈ [τ] = {1, …, τ} → t : Fin τ (0-based); reason: Lean convention; same instances
--   - encoding: max(‖(z, w)‖_∞, n) ≤ T → three conjuncts, |z_j| ≤ T, |w_j| ≤ T and n ≤ T; reason: the same inequality, coordinate by coordinate
--   - encoding: a fixed candidate tuple R (§3.4) → R : Cand I with IsCandidate I R (duplicate-free lists); reason: a finite set given by a listing; only the sets matter
--   - reading: P^(1), …, P^(τ) (implicitly at least one type) → Instance.Valid requires 1 ≤ τ; reason: the paper lists τ types and its bounds contain log(τ + 1); there are no instances with τ = 0 in the source
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Lemma 11, p.14

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation

open OnlineCRS.Combine

namespace IntConeFPT

/-- **Lemma 11 (Bounding Box).**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Lemma 11, p.14: "Every point (z, w, n) ∈ K_R(γ) satisfies
max(∥(z_r^(t), w_r^(t))∥_∞, n_r^(t)) ≤ T := max{1, N_max M}, with enc(T) = |I|^{O(1)}."

Stated for a candidate tuple `R` (§3.4, p.13: "For a fixed candidate tuple R") and for every integer
`M ≥ 1` with `P^(t) ⊆ [−M, M]^{d+k}` for all `t` (the `M` of (2.1) is one),
with the encoding clause in the explicit form `bitlength(T) ≤ bitlength(N_max) + bitlength(M)`.

**Formalization Note.** `Nat.size` is the binary length. With (2.1) (`enc(M) = |I|^{O(1)}`) and
`enc(N_max) ≤ |I|` (p.11) this gives the printed `enc(T) = |I|^{O(1)}`. -/
theorem lemma_11 (I : Instance) (hI : I.Valid) (M : ℕ) (hM : 1 ≤ M)
    (hbox : ∀ t, ∀ p ∈ I.P t, InBox M p) (Nmax : ℕ) (R : Cand I) (hR : IsCandidate I R)
    (γ : ℚ) :
    (∀ ξ ∈ K I R Nmax γ, ∀ t i,
      (∀ j, |(ξ t i).1 j| ≤ ((max 1 (Nmax * M) : ℕ) : ℝ)) ∧
      (∀ j, |(ξ t i).2.1 j| ≤ ((max 1 (Nmax * M) : ℕ) : ℝ)) ∧
      (ξ t i).2.2 ≤ ((max 1 (Nmax * M) : ℕ) : ℝ)) ∧
    Nat.size (max 1 (Nmax * M)) ≤ Nat.size Nmax + Nat.size M := by sorry

end IntConeFPT

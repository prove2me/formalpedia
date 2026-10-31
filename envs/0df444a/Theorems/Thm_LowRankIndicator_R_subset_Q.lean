-- Prove2me | Theorems.Thm_LowRankIndicator_R_subset_Q
-- name    : LowRankIndicator.R_subset_Q
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:18:43.403447+00:00
-- url     : https://prove2.me/theorems/7539c33c-fe40-49db-9df8-28b3c1a4d93c
-- title:
--   Proof of Theorem 1, p.7 — $R\subseteq Q$ (corrected: $R$ uses $t\ge c^\top x$)
-- statement:
--   Let $f(x)=g(Ax)+c^\top x$ with $f(0)=0$. Then the ray set is contained in the mixed-integer set:
--
--   $$R=\{(t,x,z):t\ge c^\top x,\ Ax=0,\ x_i\ge0\ \forall i\in I_+,\ z_i=1\ \forall i\in[n]\}\subseteq Q.$$
--
--   This is the inclusion that makes the right-hand side of the main theorem a subset of $\operatorname{cl}\operatorname{conv}(Q)$.
--
--   Differences from the source:
--   - correction: R = {t ≥ 0, Ax = 0, xᵢ ≥ 0 ∀i ∈ I₊, zᵢ = 1 ∀i} in (5) → t ≥ c⊤x in place of t ≥ 0; reason: the printed inclusion is false; for n = k = 1, A = 0, g ≡ 0, c = 1, I₊ = ∅ the point (0, 1, 1) is in the printed R and not in Q; the proof itself uses (rc⊤d, rd, e) ∈ R, and the sets agree for c = 0
--   - generalization: g proper closed convex → arbitrary g : ℝᵏ → `EReal` with f(0) = 0; reason: the statement holds without these properties and specializes to the paper's g
--   - encoding: f(0) = 0, real and extended values → `objective g A c 0 = 0` in `EReal`, 0-based `Fin n`; reason: Lean conventions, same instances
-- source:
--   Han & Gómez, Compact Extended Formulations for Low-Rank Functions with Indicator Variables, arXiv:2110.14884v2, proof of Theorem 1, p.7, "R ⊆ Q"; (5), p.5 (corrected).

import Mathlib
import Definitions.Def_LowRankIndicator_Sets

namespace LowRankIndicator

/-- Han & Gómez, arXiv:2110.14884v2, proof of Theorem 1, p.7, "R ⊆ Q": under `f(0) = 0` the ray set
lies in `Q`.

**Formalization Note.** `R` is the corrected set `t ≥ c⊤x` (see `R`); the printed `R` is not
contained in `Q` when `c ≠ 0`. -/
theorem R_subset_Q {n k : ℕ} (g : (Fin k → ℝ) → EReal) (A : Matrix (Fin k) (Fin n) ℝ)
    (c : Fin n → ℝ) (Iplus : Set (Fin n)) (hf : objective g A c 0 = 0) :
    R A c Iplus ⊆ Q g A c Iplus := by sorry

end LowRankIndicator

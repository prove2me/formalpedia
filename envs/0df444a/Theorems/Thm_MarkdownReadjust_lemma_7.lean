-- Prove2me | Theorems.Thm_MarkdownReadjust_lemma_7
-- name    : MarkdownReadjust.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:46.837228+00:00
-- url     : https://prove2.me/theorems/2201a85c-ed9f-4c6d-8570-ca1a8559aae8
-- title:
--   Lemma 7 — the schedules (14)–(15) satisfy conditions (2) and (3)
-- statement:
--   Let $\lambda>0$, $T>0$, let $x_0\ge1$ be an integer, $N\ge1$ and $\alpha\in\mathbb R$. With the update times $\{t_n\}$ of (14) and the shift terms $\{\eta_n\}$ of (15):
--
--   1. (condition (2)) the shifts strictly decrease, $\eta_0>\eta_1>\dots>\eta_N$;
--   2. (condition (3)) they average to zero over the horizon,
--   $$
--   \sum_{n=0}^{N}(t_{n+1}-t_n)\,\eta_n=0 .
--   $$
--
--   Condition (2) is what makes the readjustment tilt prices downward, and condition (3) keeps the policy centred on the fluid rate $\rho^d$.
--
--   Differences from the source:
--   - generalization: α > 1/2 (fixed with (15)) → any real α; reason: the lemma's conclusion holds for every α since (ln(x₀+1))^α > 0; contains the case α > 1/2
--   - generalization: λ the arrival rate of a model satisfying A1–A3 → any λ > 0; reason: (14)–(15) involve only λ; contains the model's λ
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), Lemma 7, p.20 (conditions (2)–(3), p.10)

import Mathlib
import Definitions.Def_MarkdownReadjust_tgrid
import Definitions.Def_MarkdownReadjust_eta

namespace MarkdownReadjust

/-- **Lemma 7, p.20** (Chen–Jasin, SSRN 3740871). With the update times `{tₙ}` of (14) and the
shift terms `{ηₙ}` of (15), conditions (2) and (3) hold:
(2) `η₀ > η₁ > ⋯ > η_N`, and (3) `Σ_{n=0}^{N} (t_{n+1} − tₙ) ηₙ = 0`.

**Formalization Note.** Stated for every arrival rate `λ > 0`, integer inventory `x₀ ≥ 1`,
horizon `T > 0`, `N ≥ 1` and every real `α` (the paper fixes `α > 1/2`, which the lemma does not
use). `t₀ = 0` and `t_{N+1} = T`. -/
theorem lemma_7 (lam α : ℝ) (hlam : 0 < lam) (x : ℕ) (hx : 1 ≤ x) (τ : ℝ) (hτ : 0 < τ)
    (N : ℕ) (hN : 1 ≤ N) :
    (∀ n : ℕ, n < N → eta lam α x τ N (n + 1) < eta lam α x τ N n) ∧
      ∑ n ∈ Finset.range (N + 1), (tgrid x τ N (n + 1) - tgrid x τ N n) * eta lam α x τ N n
        = 0 := by sorry

end MarkdownReadjust

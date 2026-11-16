-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_Supplement_two_shifts_normalization
-- name    : MinimaxInterventions1429.Separable.Supplement.two_shifts_normalization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:14:52.996209+00:00
-- url     : https://prove2.me/theorems/ba3edb3a-e014-46f9-a4ad-9e5b9956f1da
-- title:
--   Lemma 5.1 — Two shifts and normalization
-- statement:
--   For arbitrary real $m\times k$ tables $L,C$, with $m,k\ge2$,
--   $$\max\{\Lambda(L+C),\Lambda(L-C)\}\ge\Lambda(C).$$
--   If $L$ is cube-valued and $\|C\|_\infty\le\tau$, then $M_C=(L+C+\tau\mathbf1)/D_\tau$ is cube-valued. Every nonnegative-tolerance $\alpha$-optimal numerical response for $L+C+D_\tau B$ is $(\alpha/D_\tau)$-optimal for $M_C+B$, and the same threshold bit remains legal. For every reconstruction $\widehat M_C$,
--   $$d_q(D_\tau\widehat M_C-C-\tau\mathbf1,L)=D_\tau d_q(\widehat M_C,M_C).$$
--   This transfers the unchanged base algorithm to shifted inputs.
--
--   Differences from the source:
--   - encoding: normalized matrices and response rescaling → explicit entrywise maps and both numerical and witness-bit implications; reason: the same affine normalization and weak threshold convention
--   - encoding: m and k indexed from 1, with m,k >= 2 → Fin m and Fin k indexed from 0, with explicit nonzero instances and m,k >= 2; reason: source column 1 is Lean column 0; dimensions and closed-simplex boundary instances are preserved
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Lemma 5.1, printed p.16 (PDF p.18)

import Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Interfaces
set_option autoImplicit false
universe u_two_shifts_normalization

noncomputable section

namespace MinimaxInterventions1429.Separable.Supplement
open MeasureTheory

theorem two_shifts_normalization
    {m k : ℕ} [NeZero m] [NeZero k] (L C : Table m k) (hm : 2 ≤ m) (hk : 2 ≤ k) :
    interaction C ≤ max (interaction (L+C)) (interaction (L-C)) ∧
    ∀ τ : ℝ, InCube L → entryNorm C ≤ τ →
      InCube (normalized L C τ) ∧
      (∀ (α : ℝ) (B : Table m k), 0 ≤ α →
        (∀ p, Optimal (L+C+dilation τ • B) α p →
          Optimal (normalized L C τ + B) (α / dilation τ) p) ∧
        (∀ (h : Fin k) (v : Bool), LegalBit (L+C) α ⟨dilation τ • B,h⟩ v →
          LegalBit (normalized L C τ) (α / dilation τ) ⟨B,h⟩ v)) ∧
      ∀ M : Table m k, quotientDist (unnormalize M C τ) L =
        dilation τ * quotientDist M (normalized L C τ) := by sorry

end MinimaxInterventions1429.Separable.Supplement

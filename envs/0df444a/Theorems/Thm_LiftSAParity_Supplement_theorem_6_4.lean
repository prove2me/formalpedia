-- Prove2me | Theorems.Thm_LiftSAParity_Supplement_theorem_6_4
-- name    : LiftSAParity.Supplement.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:16:59.130106+00:00
-- url     : https://prove2.me/theorems/c2c8ecbd-a2e5-4c63-83a2-3ba30e961fec
-- title:
--   Theorem 6.4 — the first fooling condition implies the second with error $\varepsilon+2^{-r/2}$ when $t\le r/10$
-- statement:
--   Let $\mathcal D$ be a block $d$-local distribution for a CNF formula over $n$ blocks of $\ell$ variables, and let $r,t\in\mathbb N$ with $rt\le d$ and $t\le r/10$. Suppose $\mathcal D$ satisfies the first condition of being $(r,t,\varepsilon)$-fooling (Definition 5.3 (1)). Then for every affine space $A$ of codimension $r$,
--   $$
--   \Pr_{x\sim\widetilde{\mathcal D}_{\mathrm{Cl}^t(A)}}[x\in A]\ \le\ \varepsilon+2^{-r/2}.
--   $$
--
--   So when $t\le r/10$ the second fooling condition comes for free, with error $\varepsilon+2^{-r/2}$; this is how Theorem 6.1 obtains a fully fooling distribution.
--
--   **Formalization Note** "Affine space of codimension $r$" is a nonempty affine space with `codim A = r`. $t\le r/10$ is written $10t\le r$, and $2^{-r/2}$ is a real power.
--
--   Differences from the source:
--   - encoding: r/10 ≥ t → 10 * t ≤ r in ℕ; reason: equivalent for natural numbers
--   - encoding: d-local distribution with variables replaced by blocks → IsBlockLocalDist for some CNF φ; reason: Lean convention for the paper's object; the formula is the section's fixed φ
--   - encoding: Cl^t(A), the unique inclusion-minimal set → the intersection of all sets of blocks outside which A is t-safe; reason: equal for every nonempty affine A by the proof of Lemma 5.1
--   - encoding: ε ≥ 0 (Definition 5.3) → not assumed; reason: the first fooling condition at σ = ∅, I = ∅ and A the whole cube already forces ε ≥ 0
--   - generalization: integers n, ℓ ≥ 1 (§2, p.7) → n, ℓ : ℕ, including 0; reason: if n = 0 or ℓ = 0 the only nonempty affine space is the whole cube, so r = 0, t = 0, and the claim reads 1 ≤ ε + 1, which holds since ε ≥ 0
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §6.1, Theorem 6.4, p.22, eq. (51)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_LiftSAParity_IsAffineSpace
import Definitions.Def_LiftSAParity_Supplement_IsFooling

namespace LiftSAParity

namespace Supplement

/-- **Theorem 6.4** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary
Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…), §6.1, p.22): "Let rt ≤ d and
r/10 ≥ t, and let D be a d-local distribution satisfying the first condition of being
(r, t, ε)-fooling. Then, for any co-dimension r affine space A, it holds that
Pr_{x∼D̃_{Cl^t(A)}}[x ∈ A] ≤ ε + 2^{−r/2}. (51)"

**Formalization Note** `D` is a block d-local distribution for a CNF `φ` over `n` blocks of `ℓ`
variables. `r/10 ≥ t` is `10 t ≤ r` in `ℕ`; `2^{−r/2}` is a real power. "Affine space of
codimension r" is a nonempty affine space. -/
theorem theorem_6_4 (n ℓ : ℕ) (φ : CNF (Fin n × Fin ℓ)) (r t d : ℕ) (ε : ℝ)
    (D : (I : Finset (Fin n)) → BlockAssign n ℓ I → ℝ)
    (hD : IsBlockLocalDist φ d D) (hrt : r * t ≤ d) (htr : 10 * t ≤ r)
    (h1 : FoolCond1 d r t ε D) :
    ∀ A : Set (Fin n × Fin ℓ → ZMod 2), IsAffineSpace A → A.Nonempty → codim A = r →
      extProb D (tClosure t A) A ≤ ε + (2 : ℝ) ^ (-(r : ℝ) / 2) := by sorry

end Supplement

end LiftSAParity

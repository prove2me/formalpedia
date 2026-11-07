-- Prove2me | Theorems.Thm_LiftSAParity_claim_4_3_restrictive
-- name    : LiftSAParity.claim_4_3_restrictive
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:11:07.706305+00:00
-- url     : https://prove2.me/theorems/b9a38172-ea87-4101-bd9d-6dad86cf4312
-- title:
--   Claim 4.3 — a more restrictive space's blocks measure the same
-- statement:
--   Let $\mathcal D$ be a $d$-local distribution for $F$ and $\gamma$ any family of inputs. Let $B\subseteq A$ be nonempty affine spaces and fix $J\in[\ell]^n$. If $I_B:=I(J,B)$ satisfies $|I_B|<d$, then $I(J,A)\subseteq I_B$ and
--   $$\mu_J(A)=\Pr_{y\sim\tilde D^J_{I_B}}[y\in A].$$
--
--   This lets the two slices of a space and the space itself be measured with the same sampling law, which is the core of item (2).
--
--   **Formalization Note** The right-hand side is `tildeProb D γ J (blocks d J B) A`.
--
--   Differences from the source:
--   - generalization: stated under the standing hypotheses of §4 (ℓ ≥ 2, d ≥ 4ℓ, F unsatisfiable, γ stifling inputs of a 1-stifling g) → only D d-local for F; every ℓ, d and every γ; reason: the proof uses only the consistency of D; the Lean statement specializes to the printed one
--   - generalization: integers n ≥ 1 (§2, p.7) → n : ℕ, including n = 0; reason: at n = 0 the cube has a single point and the statement is degenerate; the Lean statement specializes to the printed one for n ≥ 1
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §4.2, pp.15–16, Claim 4.3

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_LiftSAParity_IsLocalDist
import Definitions.Def_LiftSAParity_IsStiflingInputs
import Definitions.Def_LiftSAParity_lift
import Definitions.Def_LiftSAParity_IsAffineSpace
import Definitions.Def_LiftSAParity_blocks
import Definitions.Def_LiftSAParity_mu

namespace LiftSAParity

/-- **Claim 4.3** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary Sherali-Adams over
Parities Size*, manuscript (sha256 cab5a032…), §4.2, p.15): "Let B ⊆ A be nonempty affine spaces, and fix some
J ∈ [ℓ]^n. If I_B := I(J, B) satisfies |I_B| < d, then I(J, A) ⊆ I_B and
µ_J(A) = Pr_{y∼D̃^J_{I_B}}[y ∈ A]."

**Formalization Note** The claim is stated for a `d`-local distribution `D` for `F` (its
consistency is what the proof uses) and every choice of inputs `γ`; the other standing hypotheses
of §4 (`ℓ ≥ 2`, `d ≥ 4ℓ`, `γ` stifling) are not assumed. -/
theorem claim_4_3_restrictive {n ℓ d : ℕ} (F : CNF (Fin n))
    (D : (I : Finset (Fin n)) → (I → Bool) → ℝ) (hD : IsLocalDist F d D)
    (γ : Fin ℓ → Bool → (Fin ℓ → Bool)) (A B : Set (Fin n × Fin ℓ → ZMod 2))
    (hA : IsAffineSpace A) (hB : IsAffineSpace B) (hBne : B.Nonempty) (hBA : B ⊆ A)
    (J : Fin n → Fin ℓ) (hcut : (blocks d J B).card < d) :
    blocks d J A ⊆ blocks d J B ∧ muJ d D γ J A = tildeProb D γ J (blocks d J B) A := by sorry

end LiftSAParity

-- Prove2me | Theorems.Thm_NoisyOWMPC_lemma_5_12
-- name    : NoisyOWMPC.lemma_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:03:29.369915+00:00
-- url     : https://prove2.me/theorems/4f4de548-b617-4773-86c5-6176cb1b8097
-- title:
--   Lemma 5.12 — unbiasedness of the release test
-- statement:
--   Let receiver $i$ have a bit $\beta_i$ satisfying noise preservation, and let $\mathrm{apx}$ be rational approximations. There is a constant $K_1$ such that for every admissible $M$ there is $\lambda_0$ such that for every $\lambda$ there is a number $p'$, with $|p'-\tfrac12|\le\eta:=K_1M^{-3}$ when $\lambda\ge\lambda_0$, satisfying, for every release state $\Theta$ of Construction 5.11,
--   $$\Pr\bigl[Q_\Theta(D_i)=1\bigr]=p',\qquad D_i\leftarrow C_i^{n}(\mathrm{Word}_{\mathrm{rel},i}(\Theta)),\ n=2dM^9 .$$
--
--   The release bit is thus a Bernoulli($p'$) bit independent of the state, which hides it from the sender.
--
--   Differences from the source:
--   - reading: a constant K₁ and a number p′ with |p′ − ½| ≤ η := K₁M^{−3} → K₁ independent of M and λ; for every λ one p′ for all states; the bound |p′ − ½| ≤ K₁M^{−3} for all λ ≥ λ₀(M); reason: at the finitely many λ where the 2^{−λ} rounding of the thresholds is not small against the tolerance a_t the consistency check may reject every query (p.21: rounding shifts each count center by o(1))
--   - generalization: fixed public rational upper approximations within 2^{−λ}, chosen deterministically → every polynomial-time computable family apx with C ≤ apx ≤ C + 2^{−λ}; reason: the paper's fixed choice is one such family; the analysis uses only these bounds (§5 Conventions, p.21)
--   - reading: 'polynomial M = M(λ)', 'even N = N(λ) ≥ λ polynomial in λ', 'public polynomially bounded parameters' (Definition 4.2) → public polynomial parameters (PolyParam): polynomially bounded and computed from 1^λ in polynomial time; reason: every polynomial in λ qualifies; the parties and simulators are polynomial-time algorithms and must compute the public parameters
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Lemma 5.12, p.27 (setting of Lemma 5.10, p.26)

import Mathlib
import Definitions.Def_NoisyOWMPC_releaseHalf
import Definitions.Def_NoisyOWMPC_accessHalf
import Definitions.Def_NoisyOWMPC_concreteHalves
import Definitions.Def_NoisyOWMPC_NoisePreserving

namespace NoisyOWMPC

/-- **Lemma 5.12 (Unbiasedness of the release test)** (Ishai, Lu, Zafar, STOC 2027 submission
(manuscript sha256 3a9569fa…), Lemma 5.12, p.27, in the setting of Lemma 5.10, p.26): "There are a
constant `K₁` and a number `p′` such that every release state `Θ` in the support satisfies
`Pr[Q_Θ(D_i) = 1] = p′`, `|p′ − ½| ≤ η := K₁M^{−3}`."

Here receiver `i` has a bit `β_i` satisfying noise preservation, `M` is an admissible row count,
`Q_Θ` is the release test of Construction 5.11 and `D_i ← C_iⁿ(Word_rel,i(Θ))`, `n = 2dM⁹`.

**Formalization Note** `K₁` depends neither on `M` nor on `λ` (it is chosen before the polynomial
`M`). For every `λ` the acceptance probability `p′` is the same for every state `Θ`; the bound
`|p′ − ½| ≤ K₁M^{−3}` holds for all `λ ≥ λ₀(M)`, since at the finitely many `λ` where the
`2^{−λ}`-rounding of the thresholds is not yet small against the tolerance `a_t` the consistency
check may reject every query (§5 Conventions, p.21: rounding "shifts each release count center by
`o(1)`"). -/
theorem lemma_5_12 {k : ℕ} {X : Type} [Fintype X] {Y : Fin k → Type} [∀ i, Fintype (Y i)]
    (C : ∀ i, DMC X (Y i)) (β : ∀ i, X → Y i → Bool) (i : Fin k)
    (hβ : NoisePreservingAt C i (β i)) (apx : ℕ → ∀ i, X → Y i → ℚ) (hapx : IsApx C apx) :
    ∃ K₁ : ℝ, ∀ M : ℕ → ℕ, AdmissibleM M → ∃ lam₀ : ℕ, ∀ lam, ∃ p' : ℝ,
      (lam₀ ≤ lam → |p' - 1 / 2| ≤ K₁ / (M lam : ℝ) ^ 3) ∧
      ∀ Θ : RelSec X M lam,
        ∑ d : Fin (nRel X M lam) → Y i,
          (∏ s, (C i).P ((releaseHalf C apx β M i).word lam Θ s) (d s)) *
            (if relQ C apx β i M lam Θ d then 1 else 0) = p' := by sorry

end NoisyOWMPC

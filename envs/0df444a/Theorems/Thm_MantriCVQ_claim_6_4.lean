-- Prove2me | Theorems.Thm_MantriCVQ_claim_6_4
-- name    : MantriCVQ.claim_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:15:13.0966+00:00
-- url     : https://prove2.me/theorems/0eb2c481-da83-4e32-905c-bfb119769bda
-- title:
--   Claim 6.4 — term deletion and width reduction
-- statement:
--   In the setting of Theorem 6.1, fix $J\ge0$. Let $\Phi^-_\rho$ be the DNF on the free variables obtained from $\Phi$ by deleting every term for which more than $J$ blocks are light and projecting the remaining terms by $\rho$. For every outcome of $\rho$ and all $z$,
--   $$\Phi^-_\rho(z)\le\Phi(\rho(z)),\qquad\mathrm{width}(\Phi^-_\rho)\le\Bigl\lfloor\frac W{t+1}\Bigr\rfloor+J.$$
--   If $\Phi(\rho(z))=1$ and $\Phi^-_\rho(z)=0$, then more than $J$ blocks are light for the first satisfied term of $\Phi$ at $\rho(z)$. This is the step that divides the width at each level of the proof of Theorem 6.5.
--
--   **Formalization Note** $\Phi^-_\rho$ is a function of $\Phi$ and the seeds, so the paper's "determined by $\Phi$ and $\rho$, and does not depend on $z$" holds by its type.
--
--   Differences from the source:
--   - generalization: a code family of degree d and m a positive multiple of eight → any map C and any m; reason: the claim holds for every outcome of the projection and does not use the code; the paper's case is a special case
--   - generalization: Phi normalized (p. 23) → any list DNF with listWidth at most W; the projection is normalized in the definition; reason: repeated and contradictory literals only increase the literal count
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claim 6.4, p. 25 (PDF p. 27)

import Mathlib
import Definitions.Def_MantriCVQ_reducedDNF
import Definitions.Def_MantriCVQ_listWidth

open QAlgorithms.Complexity SamplingAC0

namespace MantriCVQ

/-- **Claim 6.4** (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claim 6.4, p. 25 (PDF p. 27)): with `Φ⁻_ρ` the DNF on the free variables
obtained by deleting every term with more than `J` light blocks and projecting the rest, for every
outcome of `ρ` and all `z`: `Φ⁻_ρ(z) ≤ Φ(ρ(z))` and `width(Φ⁻_ρ) ≤ ⌊W/(t + 1)⌋ + J`; and if `Φ(ρ(z)) = 1`
and `Φ⁻_ρ(z) = 0`, then more than `J` blocks are light for the first satisfied term of `Φ` at `ρ(z)`.

**Formalization Note** `reducedDNF` is a function of `Φ` and the seeds, so "determined by `Φ` and `ρ`, and
does not depend on `z`" holds by its type. Its width is that of the normalized projection (§3, p. 13). -/
theorem claim_6_4 (C : (m : ℕ) → Bits m → Bits m → Bool) {K m W : ℕ} (t J : ℕ)
    (Φ : DNF (Fin K × Addr [m])) (hΦ : listWidth Φ ≤ W) (s : Fin K → Seed [m]) :
    listWidth (reducedDNF C t J Φ s) ≤ W / (t + 1) + J ∧
      ∀ z : Fin K → Bool,
        (DNF.eval (reducedDNF C t J Φ s) z = true → DNF.eval Φ (forestInput C [m] s z) = true) ∧
        (DNF.eval Φ (forestInput C [m] s z) = true → DNF.eval (reducedDNF C t J Φ s) z = false →
          ∃ T, firstSatTerm Φ (forestInput C [m] s z) = some T ∧
            J < (lightBlocks t T s).card) := by sorry

end MantriCVQ

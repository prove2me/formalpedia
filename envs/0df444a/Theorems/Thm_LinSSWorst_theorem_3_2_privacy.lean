-- Prove2me | Theorems.Thm_LinSSWorst_theorem_3_2_privacy
-- name    : LinSSWorst.theorem_3_2_privacy
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:06:46.554229+00:00
-- url     : https://prove2.me/theorems/5cfea60b-239c-4c85-a469-dbe21be5e189
-- title:
--   Theorem 3.2, privacy clause — in Construction 3.1 no unauthorized coalition learns anything about the secret
-- statement:
--   Let $F$ be a finite field, $f$ an $n$-party access structure, and $[n]=L\sqcup R$ a partition into nonempty sets. Then Construction 3.1 satisfies the privacy requirement for $f$: for every coalition $x$ with $f(x)=0$ and all secrets $s,s'\in F$, when all the dealer's random elements (the pads $\omega_T$ and the additive-sharing randomness) are independent and uniform,
--   $$\Pi_x(s;r)\overset{d}{=}\Pi_x(s';r).$$
--
--   This is the privacy half of Theorem 3.2.
--
--   **Formalization Note** $R$ is `Lᶜ`. The random string is uniform on `RandIdx L → F`, and privacy is equality of the two push-forward laws.
--
--   Differences from the source:
--   - encoding: the partition [n] = L ⊔ R → `L : Finset (Fin n)` with R = Lᶜ, both nonempty; reason: same partitions
--   - encoding: Construction 3.1 as a map F^{1+ℓ_r} → F^{ℓ_1+⋯+ℓ_n} → an F-linear map on the finite index types `RandIdx L`, `ShareIdx L i`, the last party of each additive sharing being the largest index of U; reason: numbering the index types gives Definition A.3's form; the page leaves the order of the parties of U free
--   - encoding: {0,1}ⁿ; "identical distributions over uniform r" → `Fin n → Bool`; equal push-forwards of `PMF.uniformOfFintype`; reason: same objects
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Theorem 3.2 and its proof (Privacy), pp.12–13

import Mathlib
import Definitions.Def_LinSSWorst_Realizes
import Definitions.Def_LinSSWorst_construction31

namespace LinSSWorst

/-- **Theorem 3.2, privacy clause**, pp.12–13, from O. Nir, *Resolving the Worst-Case Complexity of Linear Secret Sharing*, preprint (STOC 2027
submission, version of 2026-11-02, sha256 5521cfdb…).
For every finite field `F`, every access structure `f` over `[n]` and every partition
`[n] = L ⊔ R` into nonempty sets, Construction 3.1 satisfies the privacy requirement of
Definition A.2: for every unauthorized coalition and every two secrets `s, s'`, the coalition's
shares have the same distribution when the dealer's randomness (pads and additive-sharing
randomness) is uniform.

**Formalization Note.** `R = Lᶜ`. The dealer's random string is uniform on `RandIdx L → F`, i.e.
all pads `ω_T` and all additive-sharing elements `r_{U,j}` are independent and uniform; privacy is
equality of the two push-forward laws. -/
theorem theorem_3_2_privacy {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (f : (Fin n → Bool) → Bool) (hf : IsAccessStructure f) (L : Finset (Fin n))
    (hL : L.Nonempty) (hR : Lᶜ.Nonempty) :
    Private f (construction31 F f L) := by sorry

end LinSSWorst

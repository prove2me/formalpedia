-- Prove2me | Theorems.Thm_LinSSWorst_theorem_3_2_correctness
-- name    : LinSSWorst.theorem_3_2_correctness
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:06:40.35861+00:00
-- url     : https://prove2.me/theorems/36290314-5119-400c-be84-8e06a5947af8
-- title:
--   Theorem 3.2, correctness clause — Construction 3.1 lets every authorized coalition reconstruct the secret
-- statement:
--   Let $F$ be a finite field, $f$ an $n$-party access structure, and $[n]=L\sqcup R$ a partition into nonempty sets. Then Construction 3.1 satisfies the correctness requirement for $f$: for every coalition $x$ with $f(x)=1$ there is a function $\mathrm{Recon}_x$ of the coalition's shares such that
--   $$\mathrm{Recon}_x\big(\Pi_x(s;r)\big)=s\qquad\text{for every secret } s\in F \text{ and every random string } r.$$
--
--   This is the correctness half of Theorem 3.2.
--
--   **Formalization Note** $R$ is `Lᶜ`. The scheme is `construction31 F f L` on its natural finite index types.
--
--   Differences from the source:
--   - encoding: the partition [n] = L ⊔ R → `L : Finset (Fin n)` with R = Lᶜ, both nonempty; reason: same partitions
--   - encoding: Construction 3.1 as a map F^{1+ℓ_r} → F^{ℓ_1+⋯+ℓ_n} → an F-linear map on the finite index types `RandIdx L`, `ShareIdx L i`, the last party of each additive sharing being the largest index of U; reason: numbering the index types gives Definition A.3's form; the page leaves the order of the parties of U free
--   - encoding: {0,1}ⁿ → `Fin n → Bool`; reason: same objects
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Theorem 3.2 and its proof (Correctness), p.12

import Mathlib
import Definitions.Def_LinSSWorst_Realizes
import Definitions.Def_LinSSWorst_construction31

namespace LinSSWorst

/-- **Theorem 3.2, correctness clause**, p.12, from O. Nir, *Resolving the Worst-Case Complexity of Linear Secret Sharing*, preprint (STOC 2027
submission, version of 2026-11-02, sha256 5521cfdb…).
For every finite field `F`, every access structure `f` over `[n]` and every partition
`[n] = L ⊔ R` into nonempty sets, Construction 3.1 satisfies the correctness requirement of
Definition A.2: every authorized coalition has a reconstruction function recovering the secret from
its shares, for every secret and every random string.

**Formalization Note.** `R = Lᶜ`; the partition is into nonempty sets as on the page. The scheme
is `construction31 F f L` on its natural index types. -/
theorem theorem_3_2_correctness {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (f : (Fin n → Bool) → Bool) (hf : IsAccessStructure f) (L : Finset (Fin n))
    (hL : L.Nonempty) (hR : Lᶜ.Nonempty) :
    Correct f (construction31 F f L) := by sorry

end LinSSWorst

-- Prove2me | Theorems.Thm_LinSSWorst_definition_A_5
-- name    : LinSSWorst.definition_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:06:23.313079+00:00
-- url     : https://prove2.me/theorems/575560f4-0837-4970-8784-e1c3f944e2a2
-- title:
--   Definition A.5 — additive sharing reconstructs by summing, hides from strict subsets, and is a $q$-out-of-$q$ scheme
-- statement:
--   Let $F$ be a finite field and $q=m+1\ge 1$. For additive sharing of $a\in F$ among $P_1,\dots,P_q$ with random elements $r_1,\dots,r_{q-1}$:
--   1. the shares sum to the secret: $\sum_{j=1}^{q}\mathrm{sh}_j(a;r)=a$ for every $a$ and $r$;
--   2. for every $a\in F$ and every strict subset $S\subsetneq\{P_1,\dots,P_q\}$, if $r$ is uniform on $F^{q-1}$ then the shares $(\mathrm{sh}_j(a;r))_{j\in S}$ are independent uniform elements of $F$:
--   $$\mathcal L\big((\mathrm{sh}_j(a;r))_{j\in S}\big)=\mathrm{Unif}(F^{S}),$$
--   which does not depend on $a$;
--   3. the $q$-out-of-$q$ function $x\mapsto[x_1=\cdots=x_q=1]$ is an access structure, and additive sharing is a linear secret-sharing scheme that realizes it.
--
--   These are the two properties of additive sharing used in the correctness and privacy arguments of Theorem 3.2.
--
--   **Formalization Note** The parties are `Fin (m + 1)`. The law in item 2 is the push-forward of `PMF.uniformOfFintype (Fin m → F)`, and the strict subset is a `Finset` different from `univ`.
--
--   Differences from the source:
--   - encoding: q parties P_1, …, P_q → q = m + 1 parties `Fin (m + 1)`, last party `Fin.last m`; reason: every q ≥ 1 is some m + 1, and the page's construction needs a last party
--   - encoding: "the shares held by every strict subset of U are independent uniform elements of F, independently of a" → for every a, the push-forward of the uniform law on the randomness to the shares of S equals the uniform law on S → F; reason: this is that sentence in distributional form
--   - reading: "a linear scheme for the q-out-of-q access structure" → a clause that x ↦ [all x_j = 1] is an access structure, and `Realizes` for it; reason: the page calls the q-out-of-q function an access structure; the clause states it
--   - encoding: {0,1}^q; shares in F; "identical distributions over uniform r" → `Fin (m + 1) → Bool`; share vectors of length one (`Fin 1 → F`) in `additiveMap`; equal push-forwards of `PMF.uniformOfFintype`; reason: same objects
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Definition A.5, p.30

import Mathlib
import Definitions.Def_LinSSWorst_Realizes
import Definitions.Def_LinSSWorst_additiveMap

namespace LinSSWorst

/-- **Definition A.5, the additive-sharing claim**, p.30, from O. Nir, *Resolving the Worst-Case Complexity of Linear Secret Sharing*, preprint (STOC 2027
submission, version of 2026-11-02, sha256 5521cfdb…).
For additive sharing of `a ∈ F` among `q = m + 1` parties with uniform random `r_1, …, r_{q-1}`:
1. the parties reconstruct `a` by summing their shares;
2. the shares held by every strict subset `S` of the parties are independent uniform elements of
   `F`, independently of `a`: their joint law is the uniform law on `S → F`, for every `a`;
3. additive secret sharing is a linear scheme for the `q`-out-of-`q` access structure
   `x ↦ [x_j = 1 for every j]` (which is an access structure).

**Formalization Note.** `q = m + 1` covers every `q ≥ 1`; the last party is `Fin.last m`. Each
party's share is a vector of length one (`Fin 1`). "Independent uniform, independently of `a`"
is the statement that the push-forward of the uniform law on `Fin m → F` to the strict subset's
shares is the uniform law on `S → F`, whatever `a` is. -/
theorem definition_A_5 {F : Type*} [Field F] [Fintype F] (m : ℕ) :
    (∀ (a : F) (r : Fin m → F), ∑ j, additiveShares m a r j = a) ∧
    (∀ (a : F) (S : Finset (Fin (m + 1))), S ≠ Finset.univ →
      (PMF.uniformOfFintype (Fin m → F)).map (fun r (j : S) => additiveShares m a r j) =
        PMF.uniformOfFintype (S → F)) ∧
    IsAccessStructure (fun x : Fin (m + 1) → Bool => decide (∀ j, x j = true)) ∧
    Realizes (fun x : Fin (m + 1) → Bool => decide (∀ j, x j = true)) (additiveMap F m) := by sorry

end LinSSWorst

-- Prove2me | Theorems.Thm_LovaszECCKernel_proposition_9
-- name    : LovaszECCKernel.proposition_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:56:17.122521+00:00
-- url     : https://prove2.me/theorems/aaf93c06-6b89-404a-8f6a-734bfde59619
-- title:
--   Proposition 9 — at most $p$ parts of size at most $p$, $p$ prime: $\mathrm{ecc}(G)\le p^2$
-- statement:
--   **Proposition 9.** Let $p$ be a prime and $G$ a complete multipartite graph with at most $p$ parts, each of size at most $p$. Then
--   $$\mathrm{ecc}(G)\ \le\ p^2 .$$
--
--   The cover comes from the affine lines $i\mapsto ai+b$ over $\mathrm{GF}(p)$; it replaces the Type-B cliques in Lemma 7.
--
--   Differences from the source:
--   - encoding: at most p parts → at most p non-empty parts; reason: empty parts can always be added or removed
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Proposition 9, p.37 (= PDF p.37)

import Mathlib
import Definitions.Def_LovaszECCKernel_ecc
import Definitions.Def_LovaszECCKernel_partSize

set_option autoImplicit false

namespace LovaszECCKernel

/-- **Proposition 9** (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic
Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript
sha256 a9d53ab8…), Proposition 9, p.37 (= PDF p.37)): "Let G be a complete multi-partite
graph with at most p parts, each of size at most p, where p is a prime number. Then ecc(G) ≤ p²."

**Formalization Note** "At most `p` parts" counts the non-empty parts (`parts G`); empty parts can
always be added or removed. -/
theorem proposition_9 {V : Type*} [Fintype V] (G : SimpleGraph V) (p : ℕ) (hp : p.Prime)
    (hcm : G.IsCompleteMultipartite) (hparts : (parts G).card ≤ p)
    (hsize : ∀ P ∈ parts G, P.card ≤ p) :
    ecc G ≤ p ^ 2 := by sorry

end LovaszECCKernel

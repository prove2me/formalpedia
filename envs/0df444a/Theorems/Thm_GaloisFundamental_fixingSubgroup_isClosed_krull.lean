-- Prove2me | Theorems.Thm_GaloisFundamental_fixingSubgroup_isClosed_krull
-- name    : GaloisFundamental.fixingSubgroup_isClosed_krull
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T01:10:33.985528+00:00
-- url     : https://prove2.me/theorems/aef61771-afeb-4752-ad86-3c8e1fdf6995
-- title:
--   Infinite Galois theory: $\operatorname{Gal}(E/K)$ is closed in the Krull topology
-- statement:
--   Let $E/F$ be a Galois extension, possibly infinite, and give $\operatorname{Gal}(E/F)$ the Krull topology. Then for every intermediate field $K$, the subgroup $\operatorname{Gal}(E/K)$ of automorphisms fixing $K$ pointwise is a closed subgroup of $\operatorname{Gal}(E/F)$. (This is what makes $K \mapsto \operatorname{Gal}(E/K)$ a well-defined map to closed subgroups in the infinite fundamental theorem.)
-- source:
--   Wikipedia, "Fundamental theorem of Galois theory", revision oldid=1345286594, https://en.wikipedia.org/w/index.php?title=Fundamental_theorem_of_Galois_theory&oldid=1345286594, section "Infinite case" ("One important thing one needs to check is that ... Gal(E/L) is a closed subgroup of Gal(E/F) for all intermediate fields L"; Ribes–Zalesskii, Theorem 2.11.3)

import Mathlib

namespace GaloisFundamental

theorem fixingSubgroup_isClosed_krull (k K : Type*) [Field k] [Field K] [Algebra k K]
    [IsGalois k K] (L : IntermediateField k K) :
    IsClosed (L.fixingSubgroup : Set (K ≃ₐ[k] K)) := by sorry

end GaloisFundamental

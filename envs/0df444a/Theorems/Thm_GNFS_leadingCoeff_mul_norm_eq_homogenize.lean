-- Prove2me | Theorems.Thm_GNFS_leadingCoeff_mul_norm_eq_homogenize
-- name    : GNFS.leadingCoeff_mul_norm_eq_homogenize
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T02:25:19.37999+00:00
-- url     : https://prove2.me/theorems/936d1308-effc-48c9-b898-2e9c8d4b5e8b
-- title:
--   $c_d\,N(a-b\theta) = b^d f(a/b)$
-- statement:
--   Let $f = \sum_{i=0}^d c_i x^i \in \mathbb{Z}[x]$ have degree $d$ and leading coefficient $c_d$, and suppose $f$ is irreducible over $\mathbb{Q}$. Let $\theta \in \mathbb{C}$ be a root of $f$ and write $N = N_{\mathbb{Q}(\theta)/\mathbb{Q}}$ for the field norm. Then for all integers $a, b$,
--   $$c_d \cdot N(a - b\theta) = \sum_{i=0}^{d} c_i a^i b^{d-i} = b^d f(a/b).$$
--
--   In particular, for monic $f$ the sieve value $r = b^d f(a/b)$ is exactly the norm of $a - b\theta$. This is why smoothness of $r$ controls the factorization of $a - b\theta$.
--
--   **Formalization Note** The source says "$r$ is a norm of $a-b\theta$"; this holds exactly for monic $f$. The statement records the general identity with the factor $c_d$.
-- source:
--   Wikipedia, "General number field sieve" (revision oldid=1377718368, https://en.wikipedia.org/w/index.php?title=General_number_field_sieve&oldid=1377718368), section 'Method — Generation of relation pairs (sieving)'

import Mathlib
import Definitions.Def_GNFS_defs
open Polynomial IntermediateField

namespace GNFS
theorem leadingCoeff_mul_norm_eq_homogenize (f : ℤ[X])
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (θ : ℂ) (hθ : aeval θ f = 0) (a b : ℤ) :
    (f.leadingCoeff : ℚ) *
        Algebra.norm ℚ ((a : ℚ⟮θ⟯) - (b : ℚ⟮θ⟯) * AdjoinSimple.gen ℚ θ) =
      (homogenize f a b : ℚ) := by sorry
end GNFS

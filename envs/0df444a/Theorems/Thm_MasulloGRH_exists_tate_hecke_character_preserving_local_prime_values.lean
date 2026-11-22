-- Prove2me | Theorems.Thm_MasulloGRH_exists_tate_hecke_character_preserving_local_prime_values
-- name    : MasulloGRH.exists_tate_hecke_character_preserving_local_prime_values
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T19:58:19.121167+00:00
-- url     : https://prove2.me/theorems/f9d1eb55-1f78-440d-8528-da530158acd4
-- title:
--   Transport of prime values of idele-class Hecke characters to a small isomorphic number field
-- statement:
--   Let $F$ be a number field in any Lean universe, $K$ a number field in the smallest universe, and $r:F\cong K$ a field isomorphism. For each continuous circle-valued idele class character $\chi$ of $F$ in the MasulloGRH representation, there is a unitary Tate idele character $\eta$ of $K$, trivial on principal ideles, with the same local Euler coefficients. Precisely, the height-one prime corresponding to $v$ is obtained by transporting the ideal through the induced ring isomorphism of rings of integers. At this prime the Tate coefficient is its value on the chosen uniformizer idele when unramified and zero when ramified, equal in both cases to $\chi.\mathrm{primeValue}(v)$. The statement involves only field, idele, character and prime data.
-- source:
--   Representation comparison for Masullo, The Music of the Primes, §§3.2.1 and B.6.1, and the existing square-character pole boundary leaf 4833ae58-2732-4e3a-9980-79c29db50fc2. The two platform interfaces are MasulloGRH_HeckeLFunction and MusicOfPrimes_HeckeL. The independent Tate analytic theorem ecb98452-c4d2-5b41-b576-000133eadaa1 is proved in the latter representation.

import Definitions.Def_MasulloGRH_HeckeLFunction
import Definitions.Def_MusicOfPrimes_HeckeL
open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal
open scoped Classical

theorem MasulloGRH.exists_tate_hecke_character_preserving_local_prime_values
    (F : Type*) [Field F] [NumberField F] (K : Type) [Field K] [NumberField K]
    (r : F ≃+* K) (χ : MasulloGRH.HeckeCharacter F) :
    ∃ η : MusicOfPrimes.HeckeChar K, ∀ v : HeightOneSpectrum (𝓞 F),
      let w := HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv r) v
      χ.primeValue v =
        if IsUnramifiedCharAt η.toFun w then
          ((η.toFun (uniformizerIdele K w) : ℂˣ) : ℂ) else 0 := by sorry

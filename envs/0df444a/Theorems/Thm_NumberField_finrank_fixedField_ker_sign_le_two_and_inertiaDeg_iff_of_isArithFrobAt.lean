-- Prove2me | Theorems.Thm_NumberField_finrank_fixedField_ker_sign_le_two_and_inertiaDeg_iff_of_isArithFrobAt
-- name    : NumberField.finrank_fixedField_ker_sign_le_two_and_inertiaDeg_iff_of_isArithFrobAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/6fd785e7-0481-53ef-ad1c-e57fac3d840e
-- title:
--   Sign character subextension: degree ≤ 2 and inertia degree via Frobenius
-- statement:
--   Let $E$ and $L$ be number fields with $L$ an $E$-algebra and $L/E$ Galois, and let $K$ be a number field sitting in a tower $E \to K \to L$ (so $K$ is an $E$-algebra, $L$ a $K$-algebra, and the scalar actions are compatible). Put $G = \operatorname{Gal}(L/E)$, let $H \le G$ be the subgroup fixing pointwise the image of $K$ in $L$ under the induced $E$-algebra map, let $\varepsilon : G \to \mathbb{Z}^\times$ be the composite of the permutation action of $G$ on the coset space $G/H$ with the sign homomorphism, and let $F = L^{\ker \varepsilon}$ be the intermediate field of $L/E$ fixed by $\ker\varepsilon$. The assertion is twofold: first, $\dim_E F \le 2$; second, for every nonzero prime $v$ of $\mathcal{O}_E$ whose ramification index in $\mathcal{O}_L$ equals $1$, every nonzero prime $Q$ of $\mathcal{O}_L$ lying under $v$, every $\sigma \in G$ that is an arithmetic Frobenius at $Q$, and every nonzero prime $w$ of $\mathcal{O}_F$ lying over $v$ (that is, $w$ in the fibre $\{w : w \cap \mathcal{O}_E = v\}$), one has $f(w\mid v) = 1$ if and only if $\varepsilon(\sigma) = 1$, and $f(w\mid v) = 2$ if and only if $\varepsilon(\sigma) = -1$.
--
--   This is the Galois-theoretic description of the quadratic-or-trivial subextension of $L/E$ cut out by the sign of the permutation representation of $\operatorname{Gal}(L/E)$ on the cosets of the subgroup fixing $K$ (classically $E(\sqrt{d_{K/E}})$ inside $L$), together with Hilbert ramification theory identifying the residue degree of a place of that subextension with the sign of an arithmetic Frobenius. It feeds the construction of the quadratic Hecke character attached to this subextension in the Langlands–Tunnell input, being used by the statements producing admissible twists with prescribed values on uniformiser ideles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_finrank_fixedField_ker_sign_le_two_and_inertiaDeg_iff_of_isArithFrobAt.lean

import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.GroupTheory.Perm.Sign
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg
open scoped Pointwise

open scoped Classical in

theorem NumberField.finrank_fixedField_ker_sign_le_two_and_inertiaDeg_iff_of_isArithFrobAt
    (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsGalois E L]
    (K : Type) [Field K] [NumberField K] [Algebra E K] [Algebra K L] [IsScalarTower E K L] :
    let H : Subgroup (L ≃ₐ[E] L) := (IsScalarTower.toAlgHom E K L).fieldRange.fixingSubgroup
    let ε : (L ≃ₐ[E] L) →* ℤˣ :=
      (Equiv.Perm.sign : Equiv.Perm ((L ≃ₐ[E] L) ⧸ H) →* ℤˣ).comp (MulAction.toPermHom (L ≃ₐ[E] L) ((L ≃ₐ[E] L) ⧸ H))
    let F : IntermediateField E L := IntermediateField.fixedField ε.ker
    Module.finrank E F ≤ 2 ∧
      ∀ (v : HeightOneSpectrum (𝓞 E)), Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1 →
        ∀ (Q : HeightOneSpectrum (𝓞 L)), Q.under (𝓞 E) = v →
          ∀ (σ : L ≃ₐ[E] L), IsArithFrobAt (𝓞 E) σ Q.asIdeal →
            ∀ w ∈ primeFibre E F v,
              (v.asIdeal.inertiaDeg' w.asIdeal = 1 ↔ ε σ = 1) ∧ (v.asIdeal.inertiaDeg' w.asIdeal = 2 ↔ ε σ = -1) := by sorry

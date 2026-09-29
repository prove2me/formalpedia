-- Prove2me | Theorems.Thm_LanglandsTunnell_HeckeTate_exists_archRootNumber_induced_of_finrank_eq_two
-- name    : LanglandsTunnell.HeckeTate.exists_archRootNumber_induced_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/e4324bd5-ab6f-5467-92a5-1537bfd80595
-- title:
--   Archimedean root numbers of induced data over a quadratic extension
-- statement:
--   Let $E$ be a number field and $M$ a number field extension of $E$ with $\operatorname{finrank}_E M = 2$, and let $\xi \colon (\mathbb{A}_M)^\times \to \mathbb{C}^\times$ be a character of the idele units of $M$; for an infinite place $w$ of $M$ write $\xi_w = \xi \circ \mathrm{archUnitHom}\,w$ for the composite of $\xi$ with the embedding of $(M_w)^\times$ into the idele units placing the given unit at $w$ and $1$ elsewhere (`archLocalChar`). Assume that for all distinct real places $w \neq w'$ of $M$ with the same restriction to $E$ one has $\xi_w(-1)\,\xi_{w'}(-1) = -1$. The assertion is that there exists $c_0 \in \mathbb{C}$, $c_0 \neq 0$, with the following property: for all families $a \colon \{$real places of $E\} \to \mathbb{Z}/2$, $k \colon \{$complex places of $E\} \to \mathbb{Z}$, $a' \colon \{$real places of $M\} \to \mathbb{Z}/2$ and $k' \colon \{$complex places of $M\} \to \mathbb{Z}$ such that (i) $\xi_{w'}(-1) = (-1)^{v}$ at every real place $w'$ of $M$, where $v \in \{0,1\}$ is the canonical representative of $a'(w') - a(w'|_E)$, and (ii) $|k'(w')| = 0$ if $w'|_E$ is real and $|k'(w')| = |k(w'|_E)|$ if $w'|_E$ is complex, and for all families $u_{\mathbb{R}}, u_{\mathbb{C}}$ of complex numbers indexed by the real, resp. complex, places of $E$,
--   $$\prod_{w' \text{ real}} \varepsilon(a'(w')) \cdot \prod_{w' \text{ complex}} i^{|k'(w')|} = c_0 \cdot \mathrm{archRootNumber}_E,$$
--   where $\varepsilon(a) = 1$ for $a = 0$ and $\varepsilon(a) = i$ otherwise (`signEpsilon`), and the right-hand factor is the archimedean root number over $E$ formed from the parameter $\mathrm{principal}\,(0,0,0,1)$ (`RealArchParam.oddArtin`) at every real place and the zero parameter (`ComplexArchParam.trivialArtin`) at every complex place, twisted by $u_{\mathbb{R}}, a$ and $u_{\mathbb{C}}, k$; concretely it equals $\prod_{w \text{ real}} \varepsilon(a(w))\varepsilon(a(w)+1) \cdot \prod_{w \text{ complex}} i^{2|k(w)|}$, in which the families $u_{\mathbb{R}}, u_{\mathbb{C}}$ do not in fact occur.
--
--   This is the archimedean component of the inductivity of root numbers for a character induced from a quadratic extension, in the normalisation of the epsilon factors attached to the archimedean parameters of this development: the left side is the archimedean root number over $M$ of the data determined by $\xi$, the right side that over $E$ of the two-dimensional data with odd determinant, and only the existence of a non-zero proportionality constant independent of the sign and weight data is asserted. It feeds the comparison of Hecke root numbers and conductors in [`LanglandsTunnell.exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two`](thm.html#LanglandsTunnell.exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two), which supplies the functional-equation input to the converse theorem used in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_HeckeTate_exists_archRootNumber_induced_of_finrank_eq_two.lean

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.TateGlobal NumberField.InfinitePlace LanglandsTunnell LanglandsTunnell.Converse
open scoped Classical in

theorem LanglandsTunnell.HeckeTate.exists_archRootNumber_induced_of_finrank_eq_two
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ)
    (hsign : ∀ w w' : InfinitePlace M, w ≠ w' → w.IsReal → w'.IsReal →
      w.comap (algebraMap E M) = w'.comap (algebraMap E M) →
      ((archLocalChar ξ w (-1) : ℂˣ) : ℂ) * archLocalChar ξ w' (-1) = -1) :
    ∃ c₀ : ℂ, c₀ ≠ 0 ∧
      ∀ (aR : ∀ w : InfinitePlace E, w.IsReal → ZMod 2) (kC : ∀ w : InfinitePlace E, w.IsComplex → ℤ)
        (aR' : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2)
        (kC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℤ),
        (∀ w', ∀ hw' : w'.IsReal,
          ((archLocalChar ξ w' (-1) : ℂˣ) : ℂ) =
            (-1) ^ (aR' w' hw' - aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M))).val) →
        (∀ w', ∀ hw' : w'.IsComplex,
          (kC' w' hw').natAbs = if h : (w'.comap (algebraMap E M)).IsReal then 0
            else (kC _ (InfinitePlace.not_isReal_iff_isComplex.mp h)).natAbs) →
        ∀ (uR : ∀ w : InfinitePlace E, w.IsReal → ℂ) (uC : ∀ w : InfinitePlace E, w.IsComplex → ℂ),
          ((Finset.univ : Finset {w' : InfinitePlace M // w'.IsReal}).prod
              fun w' => signEpsilon (aR' w'.1 w'.2)) *
            ((Finset.univ : Finset {w' : InfinitePlace M // w'.IsComplex}).prod
              fun w' => Complex.I ^ (kC' w'.1 w'.2).natAbs) =
          c₀ * archRootNumber E (fun _ _ => RealArchParam.oddArtin) (fun _ _ => ComplexArchParam.trivialArtin)
                uR aR uC kC := by sorry

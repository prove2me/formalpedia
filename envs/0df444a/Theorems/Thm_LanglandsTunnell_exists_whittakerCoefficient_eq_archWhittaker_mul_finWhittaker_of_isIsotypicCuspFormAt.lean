-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_whittakerCoefficient_eq_archWhittaker_mul_finWhittaker_of_isIsotypicCuspFormAt
-- name    : LanglandsTunnell.exists_whittakerCoefficient_eq_archWhittaker_mul_finWhittaker_of_isIsotypicCuspFormAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/b810a27f-f7bd-5857-b8b5-278e8a789533
-- title:
--   Pure-tensor factorisation of a Whittaker function over ℚ
-- statement:
--   Everything is over $\mathbb{Q}$ and relative to the carrier pins `productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)`, which package: the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$, the set $D$, the central group $Z=\top$ (all of $(\mathbb{A}_\mathbb{Q})^\times$), the level groups $N \mapsto \mathrm{levelOne}(N)\cap \ker(\mathrm{glArch})$, the Hecke generators $\mathrm{diag}(\pi_v,1)$ at the finite places, and, on $\mathbb{A}_\mathbb{Q}$, the additive Haar measure conditioned on the box `adelicBox ℚ`. Given a character $\xi : Z \to \mathbb{C}^\times$, an ideal $N$ of $\mathbb{Z}$, a finite set $S$ of finite places, a Hecke eigensystem $\Phi$ over $\mathbb{C}$, a function $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$, functions $W_r$ indexed by the infinite places, integers $k$ indexed by the infinite places, and $C$ on pairs (finite idele, adelic matrix), assume: $\varphi$ satisfies `IsIsotypicCuspFormAt` for these pins, $\xi$, $N$, $S$, $\Phi$ (smooth cusp automorphic with central character $\xi$ and $K_f$-smooth, continuous, right invariant under $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, a Hecke coset eigenfunction with eigenvalue $\Phi.a\,v$ at each $v \notin S$, and central eigen with eigenvalue $(\mathrm{cNorm}\,v)^{-1}\Phi.b\,v$ there); at each real infinite place $w$, the predicate `HasArchCharacterAt₀` holds for $\varphi$ with the character `archWeightCharAt hw (k w)`, the $k(w)$-th power of `archWeightOneAt hw` on `rowIsometrySubgroup₀ w.Completion`; writing $W_\varphi(g) = \int \varphi(n(x)g)\,\psi_\mathbb{Q}(-x)\,d\nu(x)$ for the first Whittaker coefficient against the standard global additive character `psiQ`, one has $W_\varphi(\mathrm{diag}(a,1)g) = \bigl(\prod_w W_r\,w(a_\infty\text{ at }w)\bigr)\cdot C(a_f,g)$ for every $a \in (\mathbb{A}_\mathbb{Q})^\times$ and every $g$ in the finite-adelic subgroup $\ker(\mathrm{glArch})$, the archimedean components being transported through `extensionEmbedding`; and $W_\varphi \neq 0$ as a function. The conclusion asserts the existence of $W_A : \mathrm{GL}_2(\mathbb{R}) \to \mathbb{C}$ and $W_f$ on the finite-adelic subgroup such that: $W_\varphi(g) = W_A(\mathrm{ratArchGL2}\,g)\cdot W_f(\mathrm{finFactor}\,g)$ for all $g$, where `ratArchGL2 g` is the real component of $g$ at the unique infinite place transported to $\mathbb{R}$ and [`RSCarrier.finFactor g`](def/LanglandsTunnell_RSCarrierSplit.html#L17) is the corresponding complementary factor in $\ker(\mathrm{glArch})$; $W_f(g) = C(1,g)$; $W_A(n(x)h) = e^{2\pi i x}W_A(h)$ for $x \in \mathbb{R}$; $W_A(z h) = \mathrm{archLocalChar}$ of $\xi$ (read as a character of $(\mathbb{A}_\mathbb{Q})^\times$ through `Subgroup.topEquiv`) at the default infinite place, evaluated at the image of $z \in \mathbb{R}^\times$ in the completion, times $W_A(h)$, for scalar matrices $z$; $W_A(h\kappa) = \mathrm{archWeightChar}_\mathbb{R}(k\,\mathrm{default})(\kappa)\,W_A(h)$ for $\kappa \in$ `rowIsometrySubgroup₀ ℝ`; $W_A(\mathrm{diag}(t,1)) = W_r(\mathrm{default})(t)$ for $t \in \mathbb{R}^\times$; and $W_A$ is continuous.
--
--   This is the pure-tensor factorisation of the Whittaker function of a cuspidal vector on $\mathrm{GL}_2$ over $\mathbb{Q}$ into its archimedean and finite parts, recording the unipotent, central and maximal-compact transformation laws of the archimedean factor together with its torus profile $W_r$, and identifying the finite factor with $C(1,\cdot)$. It supplies the archimedean and finite Whittaker data used in the Rankin–Selberg and Godement–Eisenstein integral computations over $\mathbb{Q}$ and in the arithmetic realisation of cusp forms there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_whittakerCoefficient_eq_archWhittaker_mul_finWhittaker_of_isIsotypicCuspFormAt.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_LanglandsTunnell_RSCarrierSplit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion

theorem LanglandsTunnell.exists_whittakerCoefficient_eq_archWhittaker_mul_finWhittaker_of_isIsotypicCuspFormAt
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (ξ : (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
        (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wr : InfinitePlace ℚ → ℂ → ℂ) (k : InfinitePlace ℚ → ℤ)
    (C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (_hiso : IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
        (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ N S Φ φ)
    (_harch : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ)
    (_hφW : ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
      whittakerCoefficient ℚ
          (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
            (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          NumberField.StandardAddChar.psiQ φ 1 (diagOne a * g)
        = (∏ w : InfinitePlace ℚ, Wr w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
            * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g)
    (_hW : whittakerCoefficient ℚ
        (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ 1 ≠ 0) :
    ∃ (WA : GL (Fin 2) ℝ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ),
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ
            (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
              (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ 1 g
          = WA (ratArchGL2 g) * Wf (RSCarrier.finFactor g)) ∧
      (∀ g : finiteAdelicGL2Subgroup ℚ, Wf g = C 1 (g : AdelicGL2 (𝓞 ℚ) ℚ)) ∧
      (∀ (x : ℝ) (h : GL (Fin 2) ℝ),
        WA (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * x) * WA h) ∧
      (∀ (z : ℝˣ) (h : GL (Fin 2) ℝ),
        WA (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h)
          = (TateGlobal.archLocalChar (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) default
              (Units.map (ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).symm.toMonoidHom z)
              : ℂ) * WA h) ∧
      (∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
        WA (h * κ) = (archWeightCharℝ (k default) ⟨κ, hκ⟩ : ℂ) * WA h) ∧
      (∀ t : ℝˣ, WA (diagOne t) = Wr default (t : ℝ)) ∧
      Continuous WA := by sorry

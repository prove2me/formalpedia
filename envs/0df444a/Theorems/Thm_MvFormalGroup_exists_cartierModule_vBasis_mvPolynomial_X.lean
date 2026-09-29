-- Prove2me | Theorems.Thm_MvFormalGroup_exists_cartierModule_vBasis_mvPolynomial_X
-- name    : MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/4f050798-50f7-5895-921a-cca2537ace5b
-- title:
--   Universal p-typical law with variables as structure constants
-- statement:
--   Let $p$ be a prime and $d$ a natural number, and write $R_0 = \mathbb{Z}_p[X_{(m,i,j)} : m \in \mathbb{N},\ i,j \in \mathrm{Fin}\,d]$ for the polynomial ring `MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)`. The assertion is that there exist: a $d$-dimensional formal group law $\Phi$ over $R_0$, that is, a $d$-tuple of power series in the variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ with vanishing constant term, linear part $X_i + Y_i$ in the sense that the coefficients of the single variables $\mathrm{inl}\,j$ and $\mathrm{inr}\,j$ in the $i$-th component are $\delta_{ij}$, and satisfying the associativity identity between the two substitutions into three groups of variables; a proof that $\Phi$ is commutative, i.e. that interchanging the two groups of variables fixes each component; and a family $f : \mathrm{Fin}\,d \to$ `CartierModule p Φ`, each $f_i$ being a $d$-tuple of power series in variables indexed by $\mathbb{N}$ with vanishing constant term which is a homomorphism from the Witt addition law `WittLaw.addFam p R₀` to $\Phi$ in the substitution sense, such that two conditions hold. First, the matrix whose $(i,k)$ entry is the coefficient of the first Witt variable in the $k$-th component of $f_i$ (the tangent map `CartierModule.tangent`) has unit determinant. Second, for every $i$ and every $N$ there is an element $h$ of the Cartier module with $$\mathrm{frobenius}(f_i) = \sum_{m < N} V^m\Bigl(\sum_{j} \langle X_{(m,i,j)}\rangle f_j\Bigr) + V^N h,$$ where $\mathrm{frobenius}$, $V =$ `verschiebungInt` and the homotheties $\langle a \rangle$ are the additive endomorphisms of the Cartier module obtained by precomposing a curve with the endomorphisms `verFam`, `frobPolyFam` and `teichFam a` of the Witt law, and $V^m$ denotes the $m$-fold iterate.
--
--   This is the universal case of the realisation of prescribed structure constants by a formal group law: Hazewinkel's universal $p$-typical law over a polynomial ring in the structure constants, together with a $V$-basis of its Cartier module whose Frobenius expansion has the variables themselves as coefficients. It is used by [`MvFormalGroup.exists_cartierModule_vBasis_of_frobenius_expansion`](thm.html#MvFormalGroup.exists_cartierModule_vBasis_of_frobenius_expansion), which specialises the variables to arbitrary elements of a $\mathbb{Z}_p$-algebra by base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_exists_cartierModule_vBasis_mvPolynomial_X.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X
    (p : ℕ) [Fact p.Prime] (d : ℕ) :
    ∃ (Φ : MvFormalGroup d (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p))) (_ : Φ.IsComm)
      (f : Fin d → MvFormalGroup.CartierModule p Φ),
      IsUnit (Matrix.of fun i k => MvFormalGroup.CartierModule.tangent (f i) k).det ∧
      ∀ (i : Fin d) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p Φ,
        MvFormalGroup.CartierModule.frobenius (f i) =
          (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
            (∑ j : Fin d, MvFormalGroup.CartierModule.homothety
              (MvPolynomial.X ((m : ℕ), i, j) : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)) (f j))) +
          (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] h := by sorry

-- Prove2me | Theorems.Thm_OAI_PartialPermutation_fourier_bessel
-- name    : OAI.PartialPermutation.fourier_bessel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:21:10.548226+00:00
-- url     : https://prove2.me/theorems/8880363b-952e-40df-b217-b329fdedaf00
-- title:
--   Fourier–Bessel inequality at a single irreducible unitary representation
-- statement:
--   Let $G$ be a finite group, $V$ a finite-dimensional complex inner product space of dimension $d=\dim_{\mathbb C}V$, and $\rho$ an irreducible representation of $G$ on $V$ that is unitary, $\langle\rho(g)x,\rho(g)y\rangle=\langle x,y\rangle$ for all $g\in G$ and $x,y\in V$. For $f\colon G\to\mathbb{C}$ let $\hat f(\rho)=\sum_{g\in G}f(g)\rho(g)$ be its Fourier transform at $\rho$, and let $\|A\|_{\mathrm{HS}}^2=\operatorname{Re}\operatorname{tr}(A^*A)$ denote the squared Hilbert–Schmidt norm of an operator $A$ on $V$. Then
--   $$
--   d\,\bigl\|\hat f(\rho)\bigr\|_{\mathrm{HS}}^2\le|G|\sum_{g\in G}|f(g)|^2 .
--   $$
--
--   This is the one-term version of the Plancherel formula: the contribution of a single irreducible representation to $|G|\sum_g|f(g)|^2$ is at most the whole. It turns $\ell^2$ bounds on a function into Hilbert–Schmidt bounds on its Fourier transform; applied to a function whose Fourier transform at $\rho$ is the identity, it bounds the dimension of $V$, since $\|I_V\|_{\mathrm{HS}}^2=d$.
--
--   **Formalization Note** `hsNormSq A` is the real part of `trace (adjoint A * A)`, `complexFourier ρ f` is the Fourier transform, unitarity is the hypothesis `IsUnitary ρ` and irreducibility is the instance `Representation.IsIrreducible ρ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/FourierBessel.lean#L17-L51

import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation

open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate MonoidAlgebra

theorem OAI.PartialPermutation.fourier_bessel {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) [Representation.IsIrreducible ρ]
    (f : G → ℂ) :
    (Module.finrank ℂ V : ℝ) * hsNormSq (complexFourier ρ f) ≤
      (Fintype.card G : ℝ) * ∑ g, ‖f g‖ ^ 2 := by sorry

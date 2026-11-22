-- Prove2me | Theorems.Thm_MasulloGRH_nuclearRepr_trace_comp_comm
-- name    : MasulloGRH.nuclearRepr_trace_comp_comm
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:24:47.402091+00:00
-- url     : https://prove2.me/theorems/dd80d30b-d675-4127-853b-49b2efaefd28
-- title:
--   Lemma C.3.2.2 — $\operatorname{Trace}(A_0\circ T)=\operatorname{Trace}(T\circ A_0)$ for $A_0$ nuclear, on spaces with the approximation property
-- statement:
--   **Picking up nuclear traces through a continuous linear map (trace commutation).**
--
--   All vector spaces are over $\mathbb C$. A **Banach disc** of a topological vector space $F$ is a non-empty bounded convex circled subset $B\subseteq F$ whose linear span $F_B=\bigcup_{m\ge1}mB$, normed by the Minkowski functional $p_B$ of $B$, is a Banach space. A continuous linear map $T:E\to F$ is **nuclear** if it has a **nuclear representation**
--   $$T=\sum_{n}\lambda_n\,\langle\cdot,\varphi_n\rangle\,y_n ,$$
--   that is, $Tx=\sum_n\lambda_n\varphi_n(x)\,y_n$ for all $x\in E$, where $\sum_n|\lambda_n|<\infty$, $(\varphi_n)$ is an equicontinuous sequence in the dual $E'$ and $(y_n)$ is a sequence contained in a Banach disc of $F$. If $E$ has the approximation property (the identity of $E$ is a limit of finite-rank continuous linear maps uniformly on pre-compact sets), the **nuclear trace** of a nuclear operator $A$ on $E$ is $\operatorname{Trace}(A)=\sum_m\lambda_m\langle x_m,\varphi_m\rangle$ for any nuclear representation $A=\sum_m\lambda_m\langle\cdot,\varphi_m\rangle x_m$ (it does not depend on the representation).
--
--   Let $E_1,E_2$ be Hausdorff locally convex spaces which both have the approximation property, let $T:E_1\to E_2$ be a continuous linear map and let $A_0:E_2\to E_1$ be a nuclear map. Put
--   $$A:=T\circ A_0:E_2\to E_2,\qquad A_1:=A_0\circ T:E_1\to E_1 .$$
--   Then $A_1$ and $A$ are nuclear and
--   $$\operatorname{Trace}(A_1)=\operatorname{Trace}(A).$$
--
--   In the paper $T$ is a continuous injection of $E_1$ into $E_2$, and the lemma says that a nuclear operator $A$ on $E_2$ which factors through $E_1$ picks up its trace from the subspace $E_1$; the paper uses this factorization principle to compute nuclear traces (Chapters 9, 10 and 12). Taking $T$ a linear topological automorphism of $E=E_1=E_2$ and $A_0=T^{-1}\circ A$ gives the conjugation invariance $\operatorname{Trace}(T^{-1}AT)=\operatorname{Trace}(A)$ of Proposition C.3.2.1, (C.3.2.3).
--
--   **Deviation from the source.** The paper assumes in addition that $T$ is injective; this hypothesis is superfluous and is not assumed here. The statement is the classical identity $\operatorname{Trace}(uv)=\operatorname{Trace}(vu)$ for a nuclear map $u$ and a continuous linear map $v$.
--
--   **Formalization Note.** `IsHLCS` (from `Def_MasulloGRH_LocallyConvex`) means that the topology is defined by a family of seminorms and is Hausdorff. `IsNuclearMap`, `IsNuclearRepr` and `IsBanachDisc` are the definitions of `Def_MasulloGRH_NuclearMap`: a nuclear representation consists of sequences indexed by $\mathbb N$, the series converges unconditionally in $F$ (`HasSum`), and the Minkowski functional $p_B$ is Mathlib's `gauge B`. There is no trace function in the statement: the conclusion says that every nuclear representation of $A_0\circ T$ and every nuclear representation of $T\circ A_0$ have the same trace sum `∑' m, c m * φ m (y m)` (these sums converge absolutely by `MasulloGRH.nuclearRepr_trace_eq`). `HasApproximationProperty` is the definition of `Def_TopologicalTensorProduct_ApproximationProperty`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 695, Lemma C.3.2.2, (C.3.2.5) (and p. 694, (C.3.2.3)); classical reference: R. Meyer, On a representation of the idele class group related to primes and zeros of L-functions, Duke Math. J. 127 (2005), pp. 519-595, §4, Cor. 4.7 (cited by the paper as the source of the statement and of the argument)

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_MasulloGRH_NuclearMap
import Definitions.Def_TopologicalTensorProduct_ApproximationProperty

open Filter Topology TopologicalTensorProduct
set_option autoImplicit false

namespace MasulloGRH

theorem nuclearRepr_trace_comp_comm {E₁ E₂ : Type*}
    [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
    (hE₁ : IsHLCS E₁) (hE₂ : IsHLCS E₂)
    (hAP₁ : HasApproximationProperty ℂ E₁) (hAP₂ : HasApproximationProperty ℂ E₂)
    (T : E₁ →L[ℂ] E₂) (A₀ : E₂ →L[ℂ] E₁) (hA₀ : IsNuclearMap A₀) :
    IsNuclearMap (A₀ ∘L T) ∧ IsNuclearMap (T ∘L A₀) ∧
      ∀ (c c' : ℕ → ℂ) (φ : ℕ → StrongDual ℂ E₁) (y : ℕ → E₁)
        (φ' : ℕ → StrongDual ℂ E₂) (y' : ℕ → E₂),
        IsNuclearRepr (A₀ ∘L T) c φ y → IsNuclearRepr (T ∘L A₀) c' φ' y' →
        ∑' m, c m * φ m (y m) = ∑' m, c' m * φ' m (y' m) := by sorry

end MasulloGRH

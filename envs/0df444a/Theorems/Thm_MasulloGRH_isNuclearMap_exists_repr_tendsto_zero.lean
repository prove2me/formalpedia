-- Prove2me | Theorems.Thm_MasulloGRH_isNuclearMap_exists_repr_tendsto_zero
-- name    : MasulloGRH.isNuclearMap_exists_repr_tendsto_zero
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:24:41.892669+00:00
-- url     : https://prove2.me/theorems/69d3efa3-d85b-46b7-9bcf-3bc58af665eb
-- title:
--   Lemma C.3.1.2 (refinement) — a nuclear map has a representation with $\varphi_n\to0$ uniformly on a $0$-neighbourhood and $y_n\to0$ in $F_B$
-- statement:
--   **Nuclear representations with null sequences (Lemma C.3.1.2, last assertion).**
--
--   All vector spaces are over $\mathbb C$. A **Banach disc** of a topological vector space $F$ is a non-empty bounded convex circled subset $B\subseteq F$ whose linear span $F_B=\bigcup_{m\ge1}mB$, normed by the Minkowski functional $p_B$ of $B$, is a Banach space. A continuous linear map $T:E\to F$ is **nuclear** if it has a **nuclear representation**
--   $$T=\sum_{n}\lambda_n\,\langle\cdot,\varphi_n\rangle\,y_n ,$$
--   that is, $Tx=\sum_n\lambda_n\varphi_n(x)\,y_n$ for all $x\in E$, where $\sum_n|\lambda_n|<\infty$, $(\varphi_n)$ is an equicontinuous sequence in the dual $E'$ and $(y_n)$ is a sequence contained in a Banach disc of $F$.
--
--   Let $E$ and $F$ be Hausdorff locally convex spaces and let $T:E\to F$ be a nuclear map. Then $T$ has a nuclear representation
--   $$T=\sum_{n}\lambda_n\,\langle\cdot,\varphi_n\rangle_{E,E'}\,y_n,\qquad\sum_n|\lambda_n|<\infty,$$
--   in which moreover
--
--   1. $\varphi_n\to0$ uniformly on some neighbourhood $U$ of $0$ in $E$, i.e. $\sup_{x\in U}|\varphi_n(x)|\to0$;
--   2. there is a Banach disc $B\subseteq F$ containing all $y_n$ with $y_n\to0$ in the Banach space $F_B$, i.e. $p_B(y_n)\to0$ for the Minkowski functional $p_B$ of $B$; in particular $y_n\to0$ in $F$.
--
--   For Banach spaces this recovers the description (C.2.4.2) of nuclear operators by two null sequences. Such normalized representations are what one uses to show that nuclear maps are limits of finite-rank maps uniformly on bounded sets, that they are compact, and that the nuclear trace is well defined under the approximation property.
--
--   **Formalization Note.** `IsHLCS` (from `Def_MasulloGRH_LocallyConvex`) means that the topology is defined by a family of seminorms and is Hausdorff. `IsNuclearMap`, `IsNuclearRepr` and `IsBanachDisc` are the definitions of `Def_MasulloGRH_NuclearMap`: a nuclear representation consists of sequences indexed by $\mathbb N$, the series converges unconditionally in $F$ (`HasSum`), and the Minkowski functional $p_B$ is Mathlib's `gauge B`. Uniform convergence on $U$ is `TendstoUniformlyOn`; convergence in $F_B$ is `Tendsto (fun n => gauge B (y n)) atTop (𝓝 0)`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 694, Lemma C.3.1.2 (last sentence); classical reference: H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, 2nd ed., Springer, Ch. III, 7.1, Remark

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_MasulloGRH_NuclearMap

open Filter Topology
set_option autoImplicit false

namespace MasulloGRH

theorem isNuclearMap_exists_repr_tendsto_zero {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (hE : IsHLCS E) (hF : IsHLCS F) (T : E →L[ℂ] F) (hT : IsNuclearMap T) :
    ∃ (c : ℕ → ℂ) (φ : ℕ → StrongDual ℂ E) (y : ℕ → F) (U : Set E) (B : Set F),
      IsNuclearRepr T c φ y ∧
      U ∈ 𝓝 (0 : E) ∧
      TendstoUniformlyOn (fun (n : ℕ) (x : E) => φ n x) (fun _ => (0 : ℂ)) atTop U ∧
      IsBanachDisc B ∧ (∀ n, y n ∈ B) ∧
      Tendsto (fun n => gauge B (y n)) atTop (𝓝 0) ∧
      Tendsto y atTop (𝓝 0) := by sorry

end MasulloGRH

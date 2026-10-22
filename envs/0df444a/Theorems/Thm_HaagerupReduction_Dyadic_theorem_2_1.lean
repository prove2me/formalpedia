-- Prove2me | Theorems.Thm_HaagerupReduction_Dyadic_theorem_2_1
-- name    : HaagerupReduction.Dyadic.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:28.961075+00:00
-- url     : https://prove2.me/theorems/58de7765-1c96-4706-b598-aa52dc5d55be
-- title:
--   Theorem 2.1, p. 6 — R = M ⋊_{σ^ϕ} G is the w*-closure of increasing finite subalgebras R_n, each the range of a φ̂-preserving, σ^φ̂-commuting normal faithful expectation
-- statement:
--   Let $M$ be a von Neumann algebra on $H$ with a normal faithful state $\varphi$ (in standard form, $\varphi(x) = \langle x\xi,\xi\rangle$), let $G = \bigcup_{n\ge1}2^{-n}\mathbb Z$ and let $\mathcal R = M\rtimes_{\sigma^\varphi}G$ be the crossed product on $\ell^2(G,H)$ with dual state $\hat\varphi(y) = \langle y\hat\xi,\hat\xi\rangle$, $\hat\xi = \delta_0\otimes\xi$. Let $\hat S$ be modular data of $(\mathcal R,\hat\varphi)$ ($\hat S.M = \mathcal R$, $\hat S.\xi = \hat\xi$), with modular group $\sigma^{\hat\varphi}$.
--
--   Then there exists an increasing sequence $(\mathcal R_n)$ of von Neumann subalgebras of $\mathcal R$ such that
--
--   1. each $\mathcal R_n$ is finite (every isometry in $\mathcal R_n$ is unitary);
--   2. $\bigcup_n\mathcal R_n$ is w*-dense in $\mathcal R$: its double commutant is $\mathcal R$;
--   3. for every $n$ there exists a normal faithful conditional expectation $\Phi_n$ from $\mathcal R$ onto $\mathcal R_n$ such that
--   $$\hat\varphi\circ\Phi_n = \hat\varphi\quad\text{and}\quad \sigma^{\hat\varphi}_t\circ\Phi_n = \Phi_n\circ\sigma^{\hat\varphi}_t,\qquad t\in\mathbb R.$$
--
--   This is Haagerup's reduction theorem: it approximates a (possibly type III) von Neumann algebra, after passing to the crossed product, by finite ones in a way compatible with the state and its modular group, and is the tool by which the paper transfers results on tracial noncommutative $L_p$-spaces to Haagerup $L_p$-spaces.
--
--   **Formalization Note.** The modular data of $\hat\varphi$ are a hypothesis $\hat S$; their existence is the milestone `dual_modular_data_exists`. A von Neumann subalgebra contains the identity operator (Mathlib's `VonNeumannAlgebra`), and finiteness is the published `OAI.FiniteFactor.IsFiniteAlgebra`, not finite dimension. By von Neumann's bicommutant theorem the w*-closure of the unital $*$-algebra $\bigcup_n\mathcal R_n$ is its double commutant. The sequence is indexed by $\mathbb N$ instead of $n\ge1$, which is immaterial for an existence statement.
-- source:
--   Haagerup, Junge & Xu, A reduction method for noncommutative Lp-spaces and applications, arXiv:0806.3635v2, p. 6, Theorem 2.1 (proof pp. 7–11)

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HaagerupReduction_Dyadic_Model
import Definitions.Def_FiniteFactor

namespace HaagerupReduction.Dyadic

universe u

open OAI.BoundedRecovery
open Filter Topology

/-- Theorem 2.1: the dyadic crossed product `R = M ⋊_{σ^ϕ} G` is the w*-closure of an increasing
sequence of finite von Neumann subalgebras `R_n`, each the range of a normal faithful conditional
expectation `Φ_n` with `φ̂ ∘ Φ_n = φ̂` and `σ^φ̂_t ∘ Φ_n = Φ_n ∘ σ^φ̂_t`. -/
theorem theorem_2_1 {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : StandardModularData H)
    (Sh : StandardModularData (L2G H)) (hM : Sh.M = crossedProduct S) (hxi : Sh.xi = xiHat S) :
    ∃ R : ℕ → VonNeumannAlgebra (L2G H),
      (∀ n, (R n : Set (L2G H →L[ℂ] L2G H)) ⊆ crossedProduct S) ∧
      (∀ n, (R n : Set (L2G H →L[ℂ] L2G H)) ⊆ R (n + 1)) ∧
      (∀ n, OAI.FiniteFactor.IsFiniteAlgebra (R n)) ∧
      Set.centralizer (Set.centralizer (⋃ n, (R n : Set (L2G H →L[ℂ] L2G H)))) =
        (crossedProduct S : Set (L2G H →L[ℂ] L2G H)) ∧
      ∀ n, ∃ Φ : (L2G H →L[ℂ] L2G H) → (L2G H →L[ℂ] L2G H),
        IsInvariantCondExp S Sh (R n : Set (L2G H →L[ℂ] L2G H)) Φ := by sorry

end HaagerupReduction.Dyadic

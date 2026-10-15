-- Prove2me | Theorems.Thm_OAI_BogomolovPop_conjugation_kummer_scalar
-- name    : OAI.BogomolovPop.conjugation_kummer_scalar
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T20:31:15.332709+00:00
-- url     : https://prove2.me/theorems/8772f073-5ec2-448a-a72f-02dde4a6091a
-- title:
--   Galois-compatible extensions of a field endomorphism act on Kummer classes by an $\ell$-adic unit
-- statement:
--   Let $\ell$ be a prime, let $k$ be an algebraically closed field, and let $F$ be a field extension of $k$ in which $\ell\neq0$. Fix an algebraic closure $\bar F$ and let $G_F=\operatorname{Aut}_F(\bar F)$ be the absolute Galois group with its Krull topology. Let $\mathcal G_F(\ell)$ be the maximal pro-$\ell$ quotient of $G_F$ (the quotient by the intersection of all open normal subgroups $H$ with $G_F/H$ an $\ell$-group), let $\Pi^a_\ell(F)$ be the quotient of $\mathcal G_F(\ell)$ by the closure of its commutator subgroup, and let $\pi_F:G_F\to\Pi^a_\ell(F)$ be the projection. For $x\in F^\times$ let $[x]_n$ be its class in $F^\times/(F^\times)^{\ell^n}$, and for $a\in\mathbb Z_\ell$ let $a_n\in\{0,\dots,\ell^n-1\}$ be its residue modulo $\ell^n$.
--
--   Let $\varphi:F\to F$ be a ring endomorphism and let $\beta:\bar F\to\bar F$ be a ring automorphism extending it, that is $\beta(x)=\varphi(x)$ for $x\in F$. Let $u\in\mathbb Z_\ell^\times$, and assume that for every $\sigma\in G_F$ there is $\tau\in G_F$ such that
--
--   $$
--   \beta\circ\tau=\sigma\circ\beta\ \text{ on }\bar F\qquad\text{and}\qquad \pi_F(\sigma)^{u_n}\xrightarrow[n\to\infty]{}\pi_F(\tau)\ \text{ in }\Pi^a_\ell(F).
--   $$
--
--   Then there is an $\ell$-adic unit $a\in\mathbb Z_\ell^\times$ such that
--
--   $$
--   [\varphi(f)]_n=[f]_n^{\,a_n}\qquad\text{for all }f\in F^\times\text{ and all }n\ge0 .
--   $$
--
--   In words: if conjugation by $\beta$ turns the Galois action into the $u$-th power map on $\Pi^a_\ell(F)$, then $\varphi$ acts on all Kummer groups $F^\times/(F^\times)^{\ell^n}$ by one and the same $\ell$-adic unit. This converts a Galois-theoretic compatibility into an arithmetic condition on $\varphi$, which the rigidity theorem for endomorphisms acting on Kummer classes by a scalar then turns into the statement that $\varphi$ is a power of Frobenius.
--
--   **Formalization Note** $G_F$ is `AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F`, $\pi_F$ is `absoluteToPiA ℓ F`, the convergence is a `Tendsto` along `atTop`, $u_n$ is `PadicInt.appr u n`, and the conclusion is `KummerScalarLevels ℓ a f (φ f)`. Neither $\varphi$ nor $\beta$ is required to fix $k$, and no finiteness condition on $F$ is imposed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/BogomolovPop/Kummer.lean#L624-L689

import Mathlib
import Definitions.Def_BogomolovPopInjectivity
import Definitions.Def_OAI_Algebra_BogomolovPop_Foundations
import Definitions.Def_OAI_Algebra_BogomolovPop_Canonical
import Definitions.Def_OAI_Algebra_BogomolovPop_PowerCompletion
import Definitions.Def_OAI_Algebra_BogomolovPop_Kummer

open OAI OAI.BogomolovPop
open scoped Topology
open scoped Topology
open Filter

theorem OAI.BogomolovPop.conjugation_kummer_scalar (ell : ℕ) [Fact ell.Prime]
    (k F : Type*) [Field k] [Field F] [Algebra k F] [IsAlgClosed k]
    (hchar : (ell : F) ≠ 0) (φ : F →+* F)
    (β : AlgebraicClosure F ≃+* AlgebraicClosure F)
    (hβ : ∀ x : F, β (algebraMap F (AlgebraicClosure F) x) =
      algebraMap F (AlgebraicClosure F) (φ x))
    (u : (PadicInt ell)ˣ)
    (hg : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      ∃ τ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
        (∀ x, β (τ x) = σ (β x)) ∧
        Tendsto (fun n : ℕ => absoluteToPiA ell F σ ^ (u : PadicInt ell).appr n)
          atTop (nhds (absoluteToPiA ell F τ))) :
    ∃ a : (PadicInt ell)ˣ, ∀ f : Fˣ,
      KummerScalarLevels ell (a : PadicInt ell) f (Units.map φ.toMonoidHom f) := by sorry

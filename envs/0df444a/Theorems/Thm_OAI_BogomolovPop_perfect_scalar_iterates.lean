-- Prove2me | Theorems.Thm_OAI_BogomolovPop_perfect_scalar_iterates
-- name    : OAI.BogomolovPop.perfect_scalar_iterates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T20:32:57.02417+00:00
-- url     : https://prove2.me/theorems/439e1263-d1b5-4fcb-8c78-c16403da6666
-- title:
--   Galois-compatible automorphisms of the perfect closure are Frobenius twists
-- statement:
--   Let $\ell$ be a prime and $k$ an algebraically closed field. Let $F$ be a field extension of $k$ that is essentially of finite type over $k$ (finitely generated as a field), contains an element transcendental over $k$, and satisfies $\ell\neq0$ in $F$. Let $q$ be the exponential characteristic of $F$: $q=1$ if $F$ has characteristic $0$, and $q=p$ if $F$ has characteristic $p>0$. Fix an algebraic closure $\bar F$ and let $F^{\mathrm{perf}}\subseteq\bar F$ be the perfect closure of $F$. Let $G_F=\operatorname{Aut}_F(\bar F)$, let $\Pi^a_\ell(F)$ be the quotient of the maximal pro-$\ell$ quotient of $G_F$ by the closure of its commutator subgroup, and let $\pi_F:G_F\to\Pi^a_\ell(F)$ be the projection. For $u\in\mathbb Z_\ell$ let $u_n\in\{0,\dots,\ell^n-1\}$ be its residue modulo $\ell^n$.
--
--   Let $\delta:F^{\mathrm{perf}}\to F^{\mathrm{perf}}$ be a ring automorphism that maps the image of $k$ onto itself, and let $\beta:\bar F\to\bar F$ be a ring automorphism extending $\delta$. Let $u\in\mathbb Z_\ell^\times$, and assume that for every $\sigma\in G_F$ there is $\tau\in G_F$ with
--
--   $$
--   \beta\circ\tau=\sigma\circ\beta\ \text{ on }\bar F\qquad\text{and}\qquad \pi_F(\sigma)^{u_n}\xrightarrow[n\to\infty]{}\pi_F(\tau)\ \text{ in }\Pi^a_\ell(F).
--   $$
--
--   Then there are $n,m\in\mathbb N$ such that
--
--   $$
--   \delta(x)^{q^n}=x^{q^m}\qquad\text{for all }x\in F^{\mathrm{perf}} .
--   $$
--
--   Since $x\mapsto x^q$ is an automorphism $\mathrm{Fr}_q$ of the perfect field $F^{\mathrm{perf}}$, the conclusion says that $\delta=\mathrm{Fr}_q^{\,m-n}$ is an integral power of Frobenius; in characteristic $0$ it says that $\delta$ is the identity. This is the self-map case of injectivity: an automorphism of the perfect closure whose extension to $\bar F$ intertwines the Galois action with an $\ell$-adic power map on $\Pi^a_\ell(F)$ is trivial up to Frobenius.
--
--   **Formalization Note** $\delta$ is an element of `PerfectIsom k F k F`, so the condition on $k$ is that $\delta$ maps the image of $k$ in `PerfectFieldClosure F` onto itself; $q$ is given by `[ExpChar F q]`, and $u_n$ is `PadicInt.appr u n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/BogomolovPop/Injectivity.lean#L143-L207

import Mathlib
import Definitions.Def_BogomolovPopInjectivity
import Definitions.Def_OAI_Algebra_BogomolovPop_Foundations
import Definitions.Def_OAI_Algebra_BogomolovPop_Canonical
import Definitions.Def_OAI_Algebra_BogomolovPop_PowerCompletion
import Definitions.Def_OAI_Algebra_BogomolovPop_Kummer
import Definitions.Def_OAI_Algebra_BogomolovPop_Injectivity

open OAI OAI.BogomolovPop
open scoped Topology
open scoped Topology

theorem OAI.BogomolovPop.perfect_scalar_iterates (ell : ℕ) [Fact ell.Prime]
    (k F : Type*) [Field k] [Field F] [Algebra k F] [IsAlgClosed k]
    [Algebra.EssFiniteType k F] (hchar : (ell : F) ≠ 0)
    (q : ℕ) [ExpChar F q] (δ : PerfectIsom k F k F)
    (β : AlgebraicClosure F ≃+* AlgebraicClosure F)
    (hβ : ∀ x : PerfectFieldClosure F, β x = (δ.1 x : AlgebraicClosure F))
    (u : (PadicInt ell)ˣ)
    (hg : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      ∃ τ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
        (∀ x, β (τ x) = σ (β x)) ∧
        Filter.Tendsto (fun n : ℕ => absoluteToPiA ell F σ ^ (u : PadicInt ell).appr n)
          Filter.atTop (nhds (absoluteToPiA ell F τ)))
    (hx : ∃ x : F, Transcendental k x) :
    ∃ n m : ℕ, ∀ x : PerfectFieldClosure F, (δ.1 x) ^ (q ^ n) = x ^ (q ^ m) := by sorry

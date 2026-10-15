-- Prove2me | Theorems.Thm_OAI_BogomolovPop_kummer_endomorphism_frobenius
-- name    : OAI.BogomolovPop.kummer_endomorphism_frobenius
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T20:29:27.708714+00:00
-- url     : https://prove2.me/theorems/9d328466-83de-4c39-81ee-711c41b8f2cf
-- title:
--   Field endomorphisms acting on all Kummer classes by an $\ell$-adic unit are Frobenius powers
-- statement:
--   Let $\ell$ be a prime and $k$ an algebraically closed field. Let $F$ be a field extension of $k$ that is essentially of finite type over $k$ (that is, finitely generated as a field over $k$) and contains at least one element transcendental over $k$. For $n\ge0$ and $x\in F^\times$ write $[x]_n$ for the class of $x$ in the group $F^\times/(F^\times)^{\ell^n}$, and for an $\ell$-adic integer $a\in\mathbb Z_\ell$ let $a_n\in\{0,1,\dots,\ell^n-1\}$ be the residue of $a$ modulo $\ell^n$.
--
--   Let $\varphi:F\to F$ be a ring endomorphism (not assumed to fix $k$) and let $a\in\mathbb Z_\ell^\times$ be an $\ell$-adic unit such that $\varphi$ acts on every Kummer quotient as the $a$-th power map:
--
--   $$
--   [\varphi(u)]_n=[u]_n^{\,a_n}\qquad\text{for all }u\in F^\times\text{ and all }n\ge0 .
--   $$
--
--   Then either $\varphi=\mathrm{id}_F$, or there are a prime $p$ with $p=0$ in $F$ (so $F$ has characteristic $p$) and an integer $r\ge0$ such that
--
--   $$
--   \varphi(x)=x^{p^r}\qquad\text{for all }x\in F .
--   $$
--
--   Thus an endomorphism of a finitely generated, non-algebraic extension of an algebraically closed field that acts on $\ell$-adic Kummer theory by a unit scalar is the identity or a power of Frobenius. This is the field-theoretic rigidity step in recovering function fields from their abelian pro-$\ell$ Galois data, where Frobenius twists are exactly the expected ambiguity.
--
--   **Formalization Note** The hypothesis is `KummerScalarLevels ℓ a u (φ u)` for every unit `u`, and $a_n$ is `PadicInt.appr a n`. No relation between $\ell$ and the characteristic of $F$ is assumed. In the second alternative $r=0$ is allowed, which again gives the identity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/BogomolovPop/PowerCompletion.lean#L935-L962

import Mathlib
import Definitions.Def_BogomolovPopInjectivity
import Definitions.Def_OAI_Algebra_BogomolovPop_Foundations
import Definitions.Def_OAI_Algebra_BogomolovPop_Canonical
import Definitions.Def_OAI_Algebra_BogomolovPop_PowerCompletion

open OAI OAI.BogomolovPop
open scoped Topology

theorem OAI.BogomolovPop.kummer_endomorphism_frobenius (ell : ℕ) [Fact ell.Prime]
    (k F : Type*) [Field k] [Field F] [Algebra k F] [IsAlgClosed k]
    [Algebra.EssFiniteType k F] (φ : F →+* F) (a : (PadicInt ell)ˣ)
    (hx : ∃ x : F, Transcendental k x)
    (h : ∀ u : Fˣ, KummerScalarLevels ell (a : PadicInt ell) u
      (Units.map φ.toMonoidHom u)) :
    φ = RingHom.id F ∨ ∃ p r : ℕ, p.Prime ∧ (p : F) = 0 ∧
      ∀ x : F, φ x = x ^ (p ^ r) := by sorry

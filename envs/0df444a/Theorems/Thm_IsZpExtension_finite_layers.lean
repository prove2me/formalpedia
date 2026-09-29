-- Prove2me | Theorems.Thm_IsZpExtension_finite_layers
-- name    : IsZpExtension.finite_layers
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:40:30.976984+00:00
-- url     : https://prove2.me/theorems/259583d9-2abc-40fb-951f-b00f193f4d7a
-- title:
--   Finite layers of a $\mathbb{Z}_p$-extension: unique $K_n$ with $[K_n:K]=p^n$, cyclic Galois
-- statement:
--   Let $p$ be a prime and let $L/K$ be a $\mathbb{Z}_p$-extension, i.e. a Galois extension whose Galois group $\Gamma=\mathrm{Gal}(L/K)$ is topologically isomorphic to $\mathbb{Z}_p$. Then the intermediate fields of $L/K$ of finite degree over $K$ form a single tower
--   $$
--   K = K_0 \subset K_1 \subset K_2 \subset \cdots \subset L, \qquad [K_n : K] = p^n,
--   $$
--   more precisely:
--
--   1. for every $n \ge 0$ there is exactly one intermediate field $K \subseteq K_n \subseteq L$ with $[K_n:K]=p^n$;
--   2. every intermediate field $K\subseteq M\subseteq L$ with $[M:K]<\infty$ is Galois over $K$, has cyclic Galois group $\mathrm{Gal}(M/K)$, and satisfies $[M:K]=p^n$ for some $n\ge 0$ (hence $M = K_n$ and $\mathrm{Gal}(K_n/K)\cong\mathbb{Z}/p^n\mathbb{Z}$).
--
--   This is the basic structure theorem for the layers of a $\mathbb{Z}_p$-extension: the finite layers $K_n$ are the fixed fields of the closed subgroups $\Gamma^{p^n}\cong p^n\mathbb{Z}_p$, and they are the fields to which Iwasawa's asymptotic class number formula $|A_n| = p^{\mu p^n+\lambda n+\nu}$ applies.
--
--   **Formalization Note** $[M:K]$ is `Module.finrank K M`, which is $0$ for infinite-dimensional $M$; so statement 1 quantifies over all intermediate fields. `IsZpExtension p K L` is the platform definition `Def_ZpExtension` ($L/K$ Galois and $\mathrm{Gal}(L/K)\cong \mathbb{Z}_p$ as topological groups, Krull topology).
-- source:
--   L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Springer 1997, §13.1 (discussion following the definition of a Z_p-extension: the closed subgroups of Γ ≅ Z_p are 0 and Γ^{p^n}, K_n the fixed field of Γ^{p^n}, Gal(K_n/K) ≅ Z/p^nZ); K. Iwasawa, On Γ-extensions of algebraic number fields, Bull. AMS 65 (1959), §1.

import Definitions.Def_ZpExtension
import Mathlib.FieldTheory.Galois.Infinite

theorem IsZpExtension.finite_layers {p : ℕ} [Fact p.Prime] {K L : Type*} [Field K] [Field L]
    [Algebra K L] (h : IsZpExtension p K L) :
    (∀ n : ℕ, ∃! M : IntermediateField K L, Module.finrank K M = p ^ n) ∧
    ∀ M : IntermediateField K L, FiniteDimensional K M →
      IsGalois K M ∧ IsCyclic Gal(M/K) ∧ ∃ n : ℕ, Module.finrank K M = p ^ n := by sorry

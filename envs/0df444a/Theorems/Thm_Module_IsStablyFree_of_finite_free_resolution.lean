-- Prove2me | Theorems.Thm_Module_IsStablyFree_of_finite_free_resolution
-- name    : Module.IsStablyFree.of_finite_free_resolution
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T17:27:05.720421+00:00
-- url     : https://prove2.me/theorems/10d8a68c-6855-506d-87b1-d2e16336d97a
-- title:
--   Serre's lemma: a projective module with a finite free resolution is stably free
-- statement:
--   Let $A$ be a commutative ring and let $M$ be a projective $A$-module that has a finite free resolution, that is, an exact sequence
--
--   $$0 \to F_n \xrightarrow{d_{n-1}} F_{n-1} \to \cdots \to F_1 \xrightarrow{d_0} F_0 \xrightarrow{\varepsilon} M \to 0$$
--
--   in which every $F_i$ is a finitely generated free $A$-module. Then $M$ is stably free: there is a finitely generated free $A$-module $N$ such that $M \oplus N$ is free.
--
--   This is Serre's lemma on finite free resolutions. Conversely, a finitely generated stably free module $M$ with $M \oplus A^m \cong A^k$ has the finite free resolution $0 \to A^m \to A^k \to M \to 0$, so for finitely generated projective modules having a finite free resolution is the same as being stably free. The lemma is the standard route from finite free resolutions to freeness: a stably free module of rank one is free, so an invertible ideal with a finite free resolution is principal, which is how one proves that regular local rings are unique factorization domains (Auslander–Buchsbaum).
--
--   **Formalization Note**: The resolution is a family of modules `F : ℕ → Type w` indexed by all natural numbers, with `F i` trivial (`Subsingleton (F i)`) for $i > n$, maps `d i : F (i + 1) →ₗ[A] F i` (the differential $d_i\colon F_{i+1} \to F_i$) and the augmentation `ε : F 0 →ₗ[A] M`. Exactness uses Mathlib's `Function.Exact`: `Function.Exact (d 0) ε` is exactness at $F_0$, `Function.Exact (d (i + 1)) (d i)` is exactness at $F_{i+1}$ for every `i`, and `hε` says that $\varepsilon$ is surjective. Injectivity of $d_{n-1}\colon F_n \to F_{n-1}$ (of $\varepsilon$ when $n = 0$) is the exactness at $F_n$, since $F_{n+1} = 0$. Stably free is Mathlib's `Module.IsStablyFree A M`: there is a finite free `A`-module `N` such that `M × N` is free. The ring, the module $M$ and the modules $F_i$ may live in three different universes `u`, `v`, `w`.
-- source:
--   J.-P. Serre, Modules projectifs et espaces fibrés à fibre vectorielle, Séminaire P. Dubreil (1957/58), exposé 23; T. Y. Lam, Serre's Problem on Projective Modules, Springer (2006); Stacks Project, Tag 0BC4 (two-out-of-three for stably free modules, which gives the lemma by induction on n)

import Mathlib

set_option autoImplicit false

universe u v w

theorem Module.IsStablyFree.of_finite_free_resolution {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Projective A M]
    (n : ℕ) (F : ℕ → Type w) [∀ i, AddCommGroup (F i)] [∀ i, Module A (F i)]
    [∀ i, Module.Finite A (F i)] [∀ i, Module.Free A (F i)]
    (hF : ∀ i, n < i → Subsingleton (F i))
    (d : ∀ i, F (i + 1) →ₗ[A] F i) (ε : F 0 →ₗ[A] M) (hε : Function.Surjective ε)
    (hexact₀ : Function.Exact (d 0) ε) (hexact : ∀ i, Function.Exact (d (i + 1)) (d i)) :
    Module.IsStablyFree A M := by
  sorry

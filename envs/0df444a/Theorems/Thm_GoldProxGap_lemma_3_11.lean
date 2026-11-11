-- Prove2me | Theorems.Thm_GoldProxGap_lemma_3_11
-- name    : GoldProxGap.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:22:56.386689+00:00
-- url     : https://prove2.me/theorems/b94d7211-2e8a-4cf7-96d8-94067b9d3f08
-- title:
--   Lemma 3.11 — from common high coefficients to a received line (pole reduction)
-- statement:
--   **Lemma 3.11 (From common high coefficients to a received line).** Let $\mathbb F$ be a finite field, $D\subseteq\mathbb F$ with $|D|=N\ge2$, and $1\le K<N$. Suppose the polynomials $R+C_i\in\mathbb F[X]$, for $i$ in a nonempty index set, each have at least $T$ roots on $D$, where the $C_i$ are distinct and $\deg C_i\le K$. For $\beta\in\mathbb F\setminus D$ put
--   $$
--   f(x)=\frac{R(x)}{x-\beta},\quad g(x)=\frac1{x-\beta},\quad z_i=C_i(\beta),\quad H_i(X)=-\frac{C_i(X)-C_i(\beta)}{X-\beta}.
--   $$
--   Then $\deg H_i<K$ and $f+z_ig$ agrees with $H_i$ on at least $T$ coordinates; moreover $\mathrm{agr}_K(g)=\mathrm{CA}_K(f,g)=K$.
--
--   If each $R+C_i$ has degree $T>K$ and all its roots lie in $D$, one may instead take $\tilde f(X)=\frac{R(X)-R(\beta)}{X-\beta}$ and $\tilde z_i=(R+C_i)(\beta)$: the same witnesses and common-agreement bound apply, every $\tilde z_i$ is nonzero, and $\mathrm{agr}_K(\tilde f)\le T-1$.
--
--   More generally, for $1\le J<N$ and a polynomial $A$ with $\deg A\le J$ and $A(\beta)\ne0$, the word $g_A(x)=A(x)/(x-\beta)$ satisfies $\mathrm{agr}_J(g_A)=\mathrm{CA}_J(u,g_A)=J$ for every received word $u$.
--
--   This pole reduction turns a family of polynomials with common high part into a single received pair whose combinations have many exceptional challenges.
--
--   **Formalization Note** The index set is a nonempty type and distinctness is injectivity of $i\mapsto C_i$. Exact division by $X-\beta$ is `divByMonic`. "All roots lie in $D$" quantifies over the roots of $R+C_i$ in $\mathbb F$.
--
--   Differences from the source:
--   - encoding: a nonempty index set, the C_i distinct → a type ι with Nonempty ι and an injective family Cs : ι → F[X]; reason: same data
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Lemma 3.11, p.21

import Mathlib
import Definitions.Def_GoldProxGap_reedSolomon

open Polynomial

open scoped Classical

namespace GoldProxGap

/-- **Lemma 3.11 (From common high coefficients to a received line)**, p.21. Dao, Kominers,
Thaler, Zheng, *Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027
submission manuscript (2 November 2026, sha256 6c2d9ced…). Standing assumption of §3.1 (p.17):
`F` is a finite field and `D ⊆ F` has size `N ≥ 2`.

"Let 1 ≤ K < N, and suppose R + C_i ∈ F[X], for i in a nonempty index set, have at least T roots
on D, where the C_i are distinct and deg C_i ≤ K. For any β ∈ F \ D, put f(x) = R(x)/(x − β),
g(x) = 1/(x − β), z_i = C_i(β), H_i(X) = −(C_i(X) − C_i(β))/(X − β). Then deg H_i < K and
f + z_i g agrees with H_i on at least T coordinates. Moreover agr_K(g) = CA_K(f, g) = K. If each
R + C_i has degree T > K and all its roots lie in D, one may instead take
f̃(X) = (R(X) − R(β))/(X − β), z̃_i = (R + C_i)(β). The same witnesses and common-agreement bound
apply, every z̃_i is nonzero, and agr_K(f̃) ≤ T − 1. More generally, for 1 ≤ J < N and a polynomial
A with deg A ≤ J and A(β) ≠ 0, the word g_A(x) = A(x)/(x − β) satisfies
agr_J(g_A) = CA_J(u, g_A) = J for every received word u."

**Formalization Note.** The index set is a type `ι` with `Nonempty ι`; distinctness of the `C_i`
is injectivity. "At least `T` roots on `D`" counts points of `D`. Exact division by `X − β` is
`/ₘ (X − C β)`. "All its roots lie in `D`" is `∀ r ∈ (R + C_i).roots, r ∈ D`. -/
theorem lemma_3_11 {F : Type*} [Field F] [Fintype F] (D : Finset F) (hN : 2 ≤ D.card)
    (K : ℕ) (hK1 : 1 ≤ K) (hKN : K < D.card) (T : ℕ) {ι : Type*} [Nonempty ι]
    (R : F[X]) (Cs : ι → F[X]) (hCinj : Function.Injective Cs)
    (hCdeg : ∀ i, (Cs i).degree ≤ (K : WithBot ℕ))
    (hroots : ∀ i, T ≤ (D.filter (fun x => (R + Cs i).eval x = 0)).card)
    (β : F) (hβ : β ∉ D) :
    let f : D → F := fun x => R.eval (x : F) / ((x : F) - β)
    let g : D → F := fun x => 1 / ((x : F) - β)
    let z : ι → F := fun i => (Cs i).eval β
    let H : ι → F[X] := fun i => -((Cs i - C ((Cs i).eval β)) /ₘ (X - C β))
    (∀ i, (H i).degree < (K : WithBot ℕ) ∧ T ≤ polyAgree (f + z i • g) (H i)) ∧
    agr D K g = K ∧ CA D K f g = K ∧
    ((∀ i, (R + Cs i).natDegree = T ∧ ∀ r ∈ (R + Cs i).roots, r ∈ D) → K < T →
      let ft : D → F := fun x => ((R - C (R.eval β)) /ₘ (X - C β)).eval (x : F)
      let zt : ι → F := fun i => (R + Cs i).eval β
      (∀ i, T ≤ polyAgree (ft + zt i • g) (H i)) ∧ CA D K ft g = K ∧
      (∀ i, zt i ≠ 0) ∧ agr D K ft ≤ T - 1) ∧
    (∀ (J : ℕ), 1 ≤ J → J < D.card → ∀ A : F[X], A.degree ≤ (J : WithBot ℕ) → A.eval β ≠ 0 →
      let gA : D → F := fun x => A.eval (x : F) / ((x : F) - β)
      agr D J gA = J ∧ ∀ u : D → F, CA D J u gA = J) := by sorry

end GoldProxGap

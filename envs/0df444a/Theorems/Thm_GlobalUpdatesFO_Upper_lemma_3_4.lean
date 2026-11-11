-- Prove2me | Theorems.Thm_GlobalUpdatesFO_Upper_lemma_3_4
-- name    : GlobalUpdatesFO.Upper.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:21:08.110236+00:00
-- url     : https://prove2.me/theorems/34af24c4-8eb8-48bc-8793-19c540f938e9
-- title:
--   Lemma 3.4 — the type catalogue of TD_D is finite and computable: formulas of length ≤ N and representatives of size ≤ N
-- statement:
--   Let $\Sigma$ be a signature and $k, D \ge 1$. One can compute an integer $N = f_{3.4}(\Sigma,k,D)$ and a finite list $(\psi_i, B_i, \bar b_i)_{i=1}^m$ with $m = |\mathrm{Types}_{\Sigma,k,D}| \le N$ such that
--
--   - each $\psi_i \in \mathrm{FO}^k[\Sigma]$ (with $|\bar b_i|$ free variables) has length at most $N$;
--   - $\mathrm{Types}_{\Sigma,k,D}$ can be enumerated as $\{\tau_1,\dots,\tau_m\}$ so that each $\psi_i$ is logically equivalent to $\tau_i$ in $\mathrm{TD}_D$:
--   $$\forall A,\ \mathrm{td}(A) \le D,\ \forall \bar a:\quad A \models \psi_i(\bar a) \iff \mathrm{tp}^k(A,\bar a) = \tau_i ;$$
--   - each $(B_i, \bar b_i)$ is an annotated $\Sigma$-structure with at most $N$ elements and treedepth at most $D$ that satisfies $\psi_i$.
--
--   Formally: there is a computable $F$ mapping $(\Sigma, k, D)$ to the list $N, m$, followed for each $i$ by the code of $\psi_i$, a code of $B_i$ (on $\{0,\dots,|B_i|-1\}$), $|\bar b_i|$ and the entries of $\bar b_i$.
--
--   The lemma makes full $k$-types on bounded-treedepth structures finite objects that algorithms can store and compare; it is the basis of every normal form used in the paper.
--
--   **Formalization Note** "$m = |\mathrm{Types}_{\Sigma,k,D}|$" is stated as an injective enumeration $\tau$ of the catalogue indexed by $\{0,\dots,m-1\}$.
--
--   Differences from the source:
--   - encoding: we can compute N and the list (ψ_i, B_i, b̄_i) → ∃ F computable on List ℕ × ℕ × ℕ whose value at (Σ, k, D) is N :: m :: the concatenated codes of (ψ_i, B_i, |b̄_i|, b̄_i); reason: 'computable' read as Mathlib Computable on the list codes of signatures (lists of arities) and formulas (prefix codes)
--   - encoding: m = |Types_{Σ,k,D}| and the enumeration {τ_1, …, τ_m} → an injective τ : Fin m → Set Formula with range Types σ k D; reason: Lean convention for a finite set of size m
--   - encoding: a finite Σ-structure with universe U(A), relation names of Σ with their arities → Structure σ U on a finite type U : Type, Σ the list of arities, relation names 0, …, |Σ|−1; reason: Lean convention; every finite structure is of this form up to renaming
--   - encoding: formulas of FO^k[Σ] with r free variables x̄, up to renaming of bound variables → named-variable Formula over ℕ; IsFOk σ k r φ: WF, free variables among x_0, …, x_{r−1}, and |vars(φ) ∪ {0, …, r−1}| ≤ k; reason: the paper's definition (p. 17) with the free tuple fixed to x_0, …, x_{r−1}; renaming bound variables changes no type
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), pp. 18–19, Lemma 3.4

import Mathlib
import Definitions.Def_GlobalUpdatesFO_Upper_Structure
import Definitions.Def_GlobalUpdatesFO_Upper_Formula

namespace GlobalUpdatesFO.Upper

theorem lemma_3_4 :
    ∃ F : List ℕ × ℕ × ℕ → List ℕ, Computable F ∧
      ∀ (σ : Signature) (k D : ℕ), 1 ≤ k → 1 ≤ D →
        ∃ (N m : ℕ) (ψ : Fin m → Formula) (size : Fin m → ℕ)
          (B : (i : Fin m) → Structure σ (Fin (size i))) (r : Fin m → ℕ)
          (b : (i : Fin m) → Fin (r i) → Fin (size i)) (Bcode : Fin m → List ℕ),
          (∀ i, (B i).IsCode (Bcode i)) ∧
          F (σ, k, D) = N :: m :: (List.ofFn fun i =>
            (ψ i).code ++ Bcode i ++ r i :: List.ofFn (fun j => (b i j).val)).flatten ∧
          m ≤ N ∧
          (∀ i, IsFOk σ k (r i) (ψ i) ∧ (ψ i).len ≤ N) ∧
          (∃ τ : Fin m → Set Formula, Function.Injective τ ∧ Set.range τ = Types σ k D ∧
            ∀ i, LogEquivTypeTD σ k D (ψ i) (r i) (τ i)) ∧
          (∀ i, size i ≤ N ∧ (B i).td ≤ D ∧ Sat (B i) (ψ i) (b i)) := by sorry

end GlobalUpdatesFO.Upper

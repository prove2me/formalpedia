-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_lemma_5_5
-- name    : MultiplierAssoc206.Resolution.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:09:36.326037+00:00
-- url     : https://prove2.me/theorems/f0ba38e2-6f32-404f-b4d8-789554ff8d9e
-- title:
--   Width transfer
-- statement:
--   Let $\Phi$ be an unsatisfiable CNF over variables $X$, let $\Delta\ge1$, and let $(f)_{f\in F}$ be a finite family of Boolean functions, each $f$ depending only on a set $\mathbf x_f\subseteq X$ of at most $\Delta$ variables. For each $f$ let $Z_f$ be a fresh extension variable and $\mathrm{Def}(Z_f)$ any CNF over $\mathbf x_f\cup\{Z_f\}$ expressing the constraint $Z_f=f(\mathbf x_f)$, i.e. satisfied exactly by the assignments with $Z_f=f(\mathbf x_f)$. Then every resolution refutation $\pi$ of
--   $$\Phi^{\mathrm{ext}}=\Phi\wedge\bigwedge_{f\in F}\mathrm{Def}(Z_f)$$
--   has width
--   $$w(\pi)\ \ge\ \frac{w(\Phi\vdash\bot)}{2\Delta}.$$
--
--   With Theorem 2.1 this transfers the width lower bound for perfect matching to its star-local extension.
--
--   Differences from the source:
--   - generalization: F a set of Boolean functions → a finite indexed family of functions, in which the same function may occur under several indices with distinct extension variables; reason: a set is the special case of an injective family; the source's Φ^ext is a finite CNF, so F is finite
--   - encoding: Def(Z_f) is a CNF expressing Z_f = f(x_f), x_f a tuple of at most Δ variables of Φ → Def(Z_f) has variables in x_f ∪ {Z_f} and is satisfied exactly when Z_f = f(x_f); f depends only on the set x_f of at most Δ variables; reason: the meaning of 'a CNF expressing the constraint'; the extension variables are fresh and distinct
--   - encoding: width at least w(Φ⊢⊥)/(2Δ) → the real inequality w(Φ⊢⊥)/(2Δ) ≤ w(π) under the hypothesis 1 ≤ Δ; reason: the quotient is undefined at Δ = 0; every tuple has at least one variable in the source's use
--   - generalization: each tuple x_f consists of variables occurring in Φ → S f may contain any ambient variable of α, including variables not occurring in Φ; reason: taking S f inside the variables of Φ recovers every source instance; the width-transfer argument counts the at most Δ variables of each substituted function, regardless of whether they occur in Φ
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.9 (printed p.8), Lemma 5.5

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF

namespace MultiplierAssoc206.Resolution

/-- Lemma 5.5 (Width transfer), PDF p.9 (printed p.8). The extension variables are `Z_f`,
`f ∈ ι`, the ambient variables are `α`; `F f` is a Boolean function of the at most `Δ`
variables `S f` (which need not occur in `Φ`), and `Def(Z_f)` is any CNF over `S f ∪ {Z_f}` that is logically
equivalent to `Z_f = F f`. -/
theorem lemma_5_5 {α ι : Type} [Fintype ι] (Φ : CNF α) (hΦ : Unsatisfiable Φ)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (S : ι → Finset α) (hS : ∀ f, (S f).card ≤ Δ)
    (F : ι → (α → Bool) → Bool)
    (hF : ∀ f (a a' : α → Bool), (∀ x ∈ S f, a x = a' x) → F f a = F f a')
    (Def : ι → CNF (α ⊕ ι))
    (hDefVars : ∀ f, ∀ C ∈ Def f, ∀ l ∈ C, l.1 = Sum.inr f ∨ ∃ x ∈ S f, l.1 = Sum.inl x)
    (hDef : ∀ f (a : α ⊕ ι → Bool),
      CNFSat a (Def f) ↔ a (Sum.inr f) = F f (fun x => a (Sum.inl x)))
    (π : List (Clause (α ⊕ ι)))
    (hπ : IsRefutation (Φ.extend Def) π) :
    (refWidth Φ : ℝ) / (2 * Δ) ≤ (derivWidth π : ℝ) := by sorry

end MultiplierAssoc206.Resolution

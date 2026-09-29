-- Prove2me | Theorems.Thm_FoundationsRL_Structured_decoupling_lemma
-- name    : FoundationsRL.Structured.decoupling_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T20:17:45.119013+00:00
-- url     : https://prove2.me/theorems/0661efc7-6fdb-44b1-b039-ddd553f8ed7c
-- title:
--   Lemma 9 (Decoupling), general form — Eq. (2.24)
-- statement:
--   This theorem formalizes the general form of **Lemma 9 (Decoupling)** established in its
--   own proof (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
--   Decision Making*, arXiv:2312.16730v1, p. 32, Eq. (2.24)) — the form Chapter 4 invokes for
--   an arbitrary reference function $\bar f$ and an arbitrary distribution $\nu$ over a finite
--   model class, not just the boxed statement's posterior $\mu_t$ (Eq. (2.23)).
--
--   Fix a finite decision space $\Pi = \{1,\dots,A\}$, a finite index set $\iota$ enumerating a
--   finite model class $F \subseteq \mathbb{R}^\Pi$ via $f : \iota \to \mathbb{R}^\Pi$ (every
--   $f_i \in F$), a distribution $\nu \in \Delta(\iota)$, and a reference function $\bar f :
--   \Pi \to \mathbb{R}$. Writing $\pi_{f_i}$ for a maximizer of $f_i$ and $p$ for the marginal
--   distribution over decisions induced by drawing $i \sim \nu$ and playing $\pi_{f_i}$, the
--   lemma states
--
--   $$
--   \mathbb{E}_{i \sim \nu}\bigl[f_i(\pi_{f_i}) - \bar f(\pi_{f_i})\bigr] \le \sqrt{A \cdot \mathbb{E}_{i \sim \nu} \mathbb{E}_{\pi \sim p}\bigl[(f_i(\pi) - \bar f(\pi))^2\bigr]}.
--   $$
--
--   This is the **decoupling** step: on the left, the model index $i$ and the decision
--   $\pi_{f_i}$ are coupled (the decision depends on which model was drawn); on the right,
--   $\pi$ is drawn from the marginal $p$, independent of the specific draw of $i$.
--
--   **Formalization Note** Restated inside `FoundationsRL.Structured` (rather than imported
--   from the Chapter 2 mission's own item of the same underlying fact) because draft items
--   cannot import other chunks' drafts; the source index and page cited are the same Chapter 2
--   location. `piStar` is a hypothesized total maximizer selector, as elsewhere in this
--   series.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 32, Eq. (2.24)

import Mathlib

namespace FoundationsRL.Structured

/-- Lemma 9 (Decoupling), general form (Foster & Rakhlin, *Foundations of Reinforcement
Learning and Interactive Decision Making*, arXiv:2312.16730v1, p. 32, Eq. (2.24) — the
"more general result" the proof of Lemma 9 establishes and which Chapter 4 invokes for
arbitrary reference distributions, not just the posterior `µ_t` of the boxed statement (2.23)):
for a finite class of models `F` (indexed by `ι`, via `f : ι → (Fin A → ℝ)` with every `f i ∈
F`), any distribution `ν` over the models, and any `f̄ : Fin A → ℝ`, if `p` is the marginal
distribution over decisions induced by drawing a model `i ∼ ν` and playing its maximizer
`piStar (f i)`, then

`E_{i∼ν}[f_i(π_{f_i}) − f̄(π_{f_i})] ≤ √(A · E_{i∼ν} E_{π∼p}[(f_i(π) − f̄(π))²])`.

This is the decoupling step: on the left, the model `i` and the decision `π_{f_i}` are coupled;
on the right, `π` is drawn from the marginal `p`, independent of the specific draw of `i`. -/
theorem decoupling_lemma {A : ℕ} {ι : Type*} [Fintype ι] (F : Set (Fin A → ℝ))
    (f : ι → Fin A → ℝ) (hf : ∀ i, f i ∈ F)
    (piStar : (Fin A → ℝ) → Fin A) (hpiStar : ∀ i, ∀ π, f i π ≤ f i (piStar (f i)))
    (ν : ι → ℝ) (hν_nonneg : ∀ i, 0 ≤ ν i) (hν_sum : ∑ i, ν i = 1)
    (p : Fin A → ℝ) (hp : ∀ π, p π = ∑ i, ν i * (if piStar (f i) = π then 1 else 0))
    (fbar : Fin A → ℝ) :
    ∑ i, ν i * (f i (piStar (f i)) - fbar (piStar (f i))) ≤
      Real.sqrt ((A : ℝ) * ∑ i, ν i * ∑ π, p π * (f i π - fbar π) ^ 2) := by sorry

end FoundationsRL.Structured

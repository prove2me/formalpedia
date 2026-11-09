-- Prove2me | Theorems.Thm_HypRecov_lemma_5_2
-- name    : HypRecov.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:38:33.481471+00:00
-- url     : https://prove2.me/theorems/de6a8dc6-2415-4234-ad70-f7b736fe944a
-- title:
--   Lemma 5.2 — two Cauchy values per pair suffice on a small core shore
-- statement:
--   Throughout, $H$ is a simple $r$-uniform hypergraph on $V=\{0,\dots,n-1\}$ with $r\ge 2$, $k\ge 3$, $K=k-1$ and $M=2^{\lceil\log_2 k\rceil-1}$ (so $M\le K<2M$); $D\subseteq E(H)$ is a set of recovered edges and $J=H-D$ the residual hypergraph; $P_0$ is a safe base partition. A **small cut** is a set $S$ with $\mathrm{cut}_H(S)<k$.
--
--   Fix a small cut $S$ with $F=\delta_J(S)$ and core $Z$, a shore $A$ with $|Z\cap A|<r$, and an edge $e\in F$ with a vertex in $A\setminus Z$. Then:
--
--   1. $e$ passes the completion test (∗): the number of available Cauchy points of $e$ is at least $2\min\{r-|P_e|,\ |U_e|-r\}$;
--   2. the available values determine $e$: for every field $\mathbb F$, injective poles $z:V\to\mathbb F$ and points $a_{f,\ell}$ ($f$ a vertex pair, $\ell\in\{1,2\}$) distinct from each other and from the poles, if an $r$-set $e'$ with $P_e\subseteq e'\subseteq U_e$ satisfies
--   $$\sum_{v\in e'}\frac1{a_{f,\ell}-z_v}=\sum_{v\in e}\frac1{a_{f,\ell}-z_v}$$
--   for every available pair $f\subseteq e$ and $\ell\in\{1,2\}$, then $e'=e$.
--
--   Together with Lemma 5.1, this says the cache recovers every boundary edge reaching outside the core on a shore where the core is small.
--
--   Differences from the source:
--   - reading: "the available fixed metadata and the computable envelope recover the complete genuine edge e" → (∗) holds for e, and e is the only r-set between P_e and U_e whose Cauchy values agree with e's at every available point; reason: the algorithm tests (∗) and interpolates; uniqueness is the content of the interpolation step (p.11); the linear solving is covered by the time bounds of Theorem 6.4 (paper.md decision 8)
--   - generalization: one characteristic-two field with distinct z_v and a_{f,ℓ} → every field, injective poles, points injective on vertex pairs and distinct from the poles; reason: the interpolation argument works in every field; the paper's field is an instance
--   - reading: cache records, edge labels and available complete lists (Proposition 4.1) → the true residual quantities avail, knownMembers, envelope, numPoints; reason: the arguments are deterministic on the cache success event (p.9), where every value read is the true one and labels are injective on T_K (paper.md decision 7)
--   - encoding: P₀ and its current coarsening P safe → P₀ safe; reason: P does not occur in the statement; P safe and coarsening P₀ imply P₀ safe, and P = P₀ is a safe coarsening
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Lemma 5.2, pp.10–11 (PDF pp.11–12); Proposition 4.1(3), p.8

import Mathlib
import Definitions.Def_HypRecov_crisp
import Definitions.Def_HypRecov_Safe
import Definitions.Def_HypRecov_envelope
import Definitions.Def_HypRecov_heavyCore

namespace HypRecov

/-- **Lemma 5.2 (Two Cauchy values per pair suffice on a small core shore).** Zhang, Chen, Shen,
*Hypergraph Recovery from Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256
719dcfff…), Lemma 5.2, p.10 (PDF p.11): "In the preceding setting, suppose |Z ∩ A| < r and e ∈ F has a
vertex in A ∖ Z. Then the available fixed metadata and the computable envelope recover the complete
genuine edge e." Cauchy values, Proposition 4.1(3), p.8: "β_{f,ℓ}(e) = Σ_{v∈e} (a_{f,ℓ} − z_v)^{−1},
ℓ ∈ {1, 2}. All vertex values z_v and pair-specific evaluation points a_{f,ℓ} are distinct elements of
one characteristic-two field."

Setting as in Lemma 5.1. Conclusion: (i) `e` passes the completion test (∗); (ii) for any field, any
injective poles `z` and any points `a_{f,ℓ}` (two per vertex pair `f`) distinct from each other and
from the poles, `e` is the only `r`-set `e'` with `P_e ⊆ e' ⊆ U_e` whose Cauchy values agree with
those of `e` at every available point of `e`.

**Formalization Note.** "Recover" is read as (i) and (ii): the algorithm tests (∗), and the values it
holds determine `e` among the candidates its envelope allows (the interpolation uniqueness of the
proof, p.11); the linear solving is covered by the time bounds of Theorem 6.4. The field is arbitrary,
which contains the paper's characteristic-two field. -/
theorem lemma_5_2 {n : ℕ} (E D : Finset (Finset (Fin n))) (r k : ℕ) (hr : 2 ≤ r) (hk : 3 ≤ k)
    (hE : ∀ e ∈ E, e.card = r) (hD : D ⊆ E) (P₀ : Fin n → Fin n) (hP₀ : Safe E k P₀)
    (S : Finset (Fin n)) (hS : cut E S < k) (A : Finset (Fin n)) (hA : A = S ∨ A = Sᶜ)
    (hZA : (heavyCore (E \ D) S (Mpow k) ∩ A).card < r)
    (e : Finset (Fin n)) (he : e ∈ bdry (E \ D) S)
    (hx : ∃ x ∈ e, x ∈ A ∧ x ∉ heavyCore (E \ D) S (Mpow k)) :
    CompletionTest r (E \ D) P₀ (Mpow k) e ∧
    ∀ (𝕜 : Type) [Field 𝕜] (z : Fin n → 𝕜) (a : Finset (Fin n) → Fin 2 → 𝕜),
      Function.Injective z →
      Set.InjOn (fun p : Finset (Fin n) × Fin 2 => a p.1 p.2) {p | p.1.card = 2} →
      (∀ f : Finset (Fin n), f.card = 2 → ∀ (ℓ : Fin 2) (v : Fin n), a f ℓ ≠ z v) →
      ∀ e' : Finset (Fin n), e'.card = r →
        knownMembers (E \ D) P₀ (Mpow k) e ⊆ e' → e' ⊆ envelope (E \ D) P₀ (Mpow k) e →
        (∀ f ∈ e.powersetCard 2, (∃ u ∈ f, ∃ v ∈ f, avail (E \ D) P₀ (Mpow k) u v) →
          ∀ ℓ : Fin 2, ∑ v ∈ e', (a f ℓ - z v)⁻¹ = ∑ v ∈ e, (a f ℓ - z v)⁻¹) →
        e' = e := by sorry

end HypRecov

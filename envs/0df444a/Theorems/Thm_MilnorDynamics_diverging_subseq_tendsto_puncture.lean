-- Prove2me | Theorems.Thm_MilnorDynamics_diverging_subseq_tendsto_puncture
-- name    : MilnorDynamics.diverging_subseq_tendsto_puncture
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T11:07:15.064655+00:00
-- url     : https://prove2.me/theorems/868925de-3079-4f6d-948c-fc736e81043a
-- title:
--   Lemma 3.5 — sequences diverging from $\mathbb C\setminus\{0,1\}$ subconverge to a puncture
-- statement:
--   Let $U\subseteq\mathbb C$ be a nonempty connected open set, and let $f_n:U\to\mathbb C\setminus\{0,1\}$ $(n\in\mathbb N)$ be holomorphic maps. Suppose the sequence $(f_n)$ **diverges locally uniformly** from $\mathbb C\setminus\{0,1\}$, i.e. for all compact $K\subseteq U$ and $K'\subseteq\mathbb C\setminus\{0,1\}$ we have $f_n(K)\cap K'=\emptyset$ for all large $n$. Then there are a subsequence $(f_{n_k})$ and a point
--   $$
--   c\in\{0,\,1,\,\infty\}=\partial\big(\mathbb C\setminus\{0,1\}\big)\subseteq\hat{\mathbb C}
--   $$
--   such that $f_{n_k}\to c$ (the constant map) locally uniformly on $U$ with respect to the chordal metric of the Riemann sphere $\hat{\mathbb C}$.
--
--   This is Milnor's Lemma 3.5 for $U=\mathbb C\setminus\{0,1\}$ inside $T=\hat{\mathbb C}$ (a sequence can never diverge from the compact surface $\hat{\mathbb C}$). It is the key step of Corollary 3.6.
--
--   **Formalization Note** The maps are functions $\mathbb C\to\mathbb C$, holomorphic on $U$ and mapping $U$ into $\mathbb C\setminus\{0,1\}$; they are viewed in $\hat{\mathbb C}$ (`OnePoint ℂ`) via the inclusion $\mathbb C\hookrightarrow\hat{\mathbb C}$. Milnor's source surface is an arbitrary Riemann surface; here it is a domain in $\mathbb C$.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §3, p. 35, Lemma 3.5, special case U = C \ {0,1} inside T = Riemann sphere, S = a domain in C

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem diverging_subseq_tendsto_puncture (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (hdiv : DivergesLocallyUniformlyFrom f U ({0, 1}ᶜ : Set ℂ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ c ∈ ({((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), ∞} : Set (OnePoint ℂ)),
        TendstoLocallyUniformlyOnSphere (fun n z => ((f (φ n) z : ℂ) : OnePoint ℂ))
          (fun _ => c) U := by sorry

end MilnorDynamics

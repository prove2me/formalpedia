-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_exists_stages
-- name    : MasulloGRH.schwartzBruhat_exists_stages
-- status  : Proved
-- author  : @Miikka
-- created : 2026-11-21T13:03:16.092287+00:00
-- url     : https://prove2.me/theorems/d409b5f9-5782-41d7-8358-62597fdca87c
-- title:
--   Bruhat: a cofinal sequence of structural pairs with compatible projections
-- statement:
--   Let $G$ be a second countable Hausdorff locally compact abelian group, and let $\mathcal S(G)$ be its Schwartz–Bruhat space with the locally convex inductive limit topology of the spaces $\mathcal S(k,\Gamma)\cong\mathcal S(\Gamma/k)$ over all structural pairs $(\Gamma,k)$.
--
--   Then there is a sequence of **stages** for $\mathcal S(G)$: for every $N\in\mathbb N$ an elementary abelian Lie group $E_N=\mathbb R^{m_N}\times\mathbb T^{n_N}\times\mathbb Z^{r_N}\times\prod_{i<s_N}\mathbb Z/d_{N,i}$ (all $d_{N,i}\neq 0$), together with linear maps
--   $$J_N\colon\mathcal S(E_N)\to\mathcal S(G),\qquad P_N\colon\mathcal S(G)\to\mathcal S(E_N),$$
--   such that:
--
--   1. each $J_N$ is the inclusion $\mathcal S(\Gamma_N/k_N)\to\mathcal S(G)$ attached to a structural pair $(\Gamma_N,k_N)$ and a presentation $\Gamma_N/k_N\cong E_N$;
--   2. $P_N\circ J_N=\mathrm{id}$, and the projections $p_N=J_N\circ P_N$ satisfy $p_M\circ p_N=p_N=p_N\circ p_M$ for $N\le M$;
--   3. every $f\in\mathcal S(G)$ satisfies $p_N f=f$ for some $N$;
--   4. for every structural pair $(\Gamma,k)$ with a presentation of $\Gamma/k$ there is an $M$ such that $p_M$ fixes the image of $\mathcal S(\Gamma/k)$ in $\mathcal S(G)$, and $P_M$ restricted to that image is continuous on $\mathcal S(\Gamma/k)$;
--   5. all the transition maps $P_N\circ J_M\colon\mathcal S(E_M)\to\mathcal S(E_N)$ are continuous.
--
--   **Formalization Note** In the source the stages come from an exhaustion of $G$ by open compactly generated subgroups $\Gamma_N$ together with decreasing good compact subgroups $k_N\subseteq\Gamma_N$, $\bigcap_N k_N=1$; $P_N$ is averaging over $k_N$ followed by restriction to $\Gamma_N$. The statement records exactly the properties of this construction that are used to show that $\mathcal S(G)$ is a strict LF-space of nuclear Fréchet spaces.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.1.5.3, proof of Theorem D.1.5.7, pp. 763–764 (and F. Bruhat, Distributions sur un groupe localement compact, Bull. SMF 89 (1961))

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhat_exists_stages
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] :
    ∃ (m n r s : ℕ → ℕ) (d : (N : ℕ) → Fin (s N) → ℕ)
      (J : (N : ℕ) → ElemSchwartz (m N) (n N) (r N) (s N) (d N) →ₗ[ℂ] SchwartzBruhat G)
      (P : (N : ℕ) → SchwartzBruhat G →ₗ[ℂ] ElemSchwartz (m N) (n N) (r N) (s N) (d N)),
      (∀ N i, d N i ≠ 0) ∧
      (∀ N y, P N (J N y) = y) ∧
      (∀ N M f, N ≤ M → J M (P M (J N (P N f))) = J N (P N f)) ∧
      (∀ N M f, N ≤ M → J N (P N (J M (P M f))) = J N (P N f)) ∧
      (∀ f, ∃ N, J N (P N f) = f) ∧
      (∀ N, ∃ (Γ k : Subgroup G)
        (π : Γ →* Multiplicative (ElemGroup (m N) (n N) (r N) (s N) (d N)))
        (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π),
        ∀ y, J N y = SchwartzBruhat.ofElem Γ k π hs hπ y) ∧
      (∀ (Γ k : Subgroup G) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
        (π : Γ →* Multiplicative (ElemGroup m' n' r' s' d')) (hs : IsStructuralPair Γ k)
        (hπ : IsElemPresentation Γ k π), ∃ M,
          (∀ g, J M (P M (SchwartzBruhat.ofElem Γ k π hs hπ g)) =
            SchwartzBruhat.ofElem Γ k π hs hπ g) ∧
          Continuous (fun g => P M (SchwartzBruhat.ofElem Γ k π hs hπ g))) ∧
      (∀ N M, Continuous (fun y => P N (J M y))) := by sorry

end MasulloGRH
